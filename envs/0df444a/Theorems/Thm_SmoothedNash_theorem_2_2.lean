-- Prove2me | Theorems.Thm_SmoothedNash_theorem_2_2
-- name    : SmoothedNash.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:58.445053+00:00
-- url     : https://prove2.me/theorems/c27f7e8b-bb21-4220-9eba-b3c4837ae3b0
-- title:
--   Theorem 2.2 — Algorithm 2 returns an $\varepsilon$-Nash equilibrium with $(1+\lceil\log_2(4m/\varepsilon)\rceil)(CmM)^{mn}$ expected evaluations
-- statement:
--   Consider finite normal-form games with $m \ge 1$ players and $n \ge 1$ actions, payoffs in $[0, 1]$, and an accuracy $0 < \varepsilon \le 1$; write $D = \lceil \log_2(4m/\varepsilon) \rceil$. Suppose that for any mixed profile $x$ the full deviation-payoff vector $U(x)$ can be computed in time $T$.
--
--   1. **Correctness.** For every such game and every processing order of the support profiles and of the frontiers, Algorithm 2 returns a point, and that point is an $\varepsilon$-approximate Nash equilibrium.
--   2. **Expected number of evaluations.** There is a universal constant $C > 1$ such that for every random game satisfying Assumption 1.18 with constant $M$ (on any probability space, with measurable payoffs) and every processing order,
--   $$
--   \mathbb E\bigl[\#\text{payoff-vector computations}\bigr] \le \Bigl(1 + \Bigl\lceil \log_2 \frac{4m}{\varepsilon} \Bigr\rceil\Bigr) (CmM)^{mn}.
--   $$
--   3. **Expected running time.** Including the work of generating the grid points and their children, for every polynomial overhead $(mn+1)^\kappa$ per unit of work and every $c > 0$ there is $C > 1$ (depending only on $\kappa$ and $c$) such that, whenever $T \ge c\,mn$,
--   $$
--   \mathbb E\bigl[\text{running time}\bigr] \le T \Bigl(1 + \Bigl\lceil \log_2 \frac{4m}{\varepsilon} \Bigr\rceil\Bigr) (CmM)^{mn}.
--   $$
--
--   The algorithm is deterministic, and the expectation is over the realized game. Compared with brute-force search over an $\varepsilon$-net of $(\Delta_n)^m$, whose size grows like $(1/\varepsilon)^{m(n-1)}$, the dependence on $\varepsilon$ is only logarithmic.
--
--   Differences from the source:
--   - reading: "for all support profiles" (line 2) and "for all c ∈ F_t(A)" (line 9), with no order fixed → every support order σ and every frontier enumeration; reason: the pseudocode fixes no order, and the theorem holds for each
--   - generalization: one deterministic algorithm, whose orders do not depend on the realized game → in clauses 2–3 the orders σ and enum may be arbitrary functions of the realized game; reason: constant orders are the special case; the evaluation and work counts are bounded pointwise by order-free quantities, so the bounds hold for each choice
--   - reading: "Including the work of generating the grid points and their children, the expected running time is at most T(1 + ⌈log₂ 4m/ε⌉)(CmM)^{mn}", with O(mn) test operations and poly(mn) coordinate operations per generated point (p.19) → runTime T κ = T·#evaluations + (mn + 1)^κ·work, with the work count of supportRun, for every κ ∈ ℕ; reason: the paper's cost model is informal; quantifying over every κ covers every polynomial overhead
--   - reading: T = Ω(mn) and "a universal constant C" (p.19) → ∀ κ, ∀ c > 0, ∃ C > 1, … ∀ T ≥ c·mn; reason: Ω(mn) means T ≥ c·mn for some c > 0; the constant absorbing the overhead may depend only on the cost-model constants κ and c
--   - encoding: the algorithm's output, a point or Fail → RunResult.out : Option, with none for Fail; reason: Lean representation of a possibly failing output
--   - encoding: the expectation E[·] of a count → the lower Lebesgue integral ∫⁻ of the count, cast to ℝ≥0∞; reason: the count is a nonnegative random variable; ∫⁻ is its expectation
--   - encoding: a random (realized) game satisfying Assumption 1.18 → a probability space (Ω, P), a random game G with measurable payoffs in [0, 1] for every ω, and BoundedDensity P G M; reason: measurability is implicit in "random game"; the density bound is the equivalent measure inequality of BoundedDensity
--   - encoding: games with payoffs u_i : [n]^m → [0, 1] (p.6) → real payoffs u with the hypothesis PayoffsIn01 u; reason: the range [0, 1] is part of the paper's game model and is stated as a hypothesis
--   - encoding: a game with m players, each with n actions (m, n ≥ 1 implicit) → hypotheses 1 ≤ m and 1 ≤ n; reason: a game has a player, and Δ_n is empty for n = 0
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Theorem 2.2, pp.14–15 (proof p.19)

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_IsEpsNash
import Definitions.Def_SmoothedNash_PayoffsIn01
import Definitions.Def_SmoothedNash_BoundedDensity
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_D
import Definitions.Def_SmoothedNash_RunResult
import Definitions.Def_SmoothedNash_IsSupportOrder
import Definitions.Def_SmoothedNash_IsFrontierEnum
import Definitions.Def_SmoothedNash_run
import Definitions.Def_SmoothedNash_runTime
open MeasureTheory
open scoped ENNReal

namespace SmoothedNash

/-- **Theorem 2.2** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.14–15). Assume Assumption 1.18, and suppose that for any mixed profile
`x` one can compute the full deviation-payoff vector `U(x)` in time `T`. Let `0 < ε ≤ 1`. Then there
exists a universal constant `C > 1` such that Algorithm 2 returns an `ε`-approximate Nash equilibrium
for every realized game. Moreover, the expected number of payoff-vector computations is at most
`(1 + ⌈log_2 (4m/ε)⌉)(CmM)^{mn}`. Including the work of generating the grid points and their
children, the expected running time is at most `T (1 + ⌈log_2 (4m/ε)⌉)(CmM)^{mn}`. The algorithm
is deterministic, and the expectation is over the realized game.

The conjunction states:
1. correctness: for every game with `m, n ≥ 1` and payoffs in `[0, 1]`, every `ε ∈ (0, 1]` and every
   processing order, the run returns a point, and it is an `ε`-Nash equilibrium;
2. expected evaluations: one universal `C > 1` such that for every random game satisfying
   Assumption 1.18 and every processing order (which may depend on the realized game),
   `E[#evaluations] ≤ (1 + D)(CmM)^{mn}`;
3. expected running time: for every cost exponent `κ` and every `c > 0` there is `C > 1` such that
   `E[runTime] ≤ T (1 + D)(CmM)^{mn}` whenever `T ≥ c·mn`.

**Formalization Note** The processing orders of line 2 (`σ`) and line 9 (`enum`) are parameters. The
running time is `T · #evaluations + (mn + 1)^κ · work` with the work count of `supportRun`, and the
paper's `T = Ω(mn)` (p.19) is `T ≥ c·mn`; `C` in clause 3 depends only on `κ` and `c`. The
expectation is the lower Lebesgue integral; `D = ⌈log_2 (4m/ε)⌉` is `D m ε`. -/
theorem theorem_2_2 :
    (∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u : Game m n, PayoffsIn01 u →
      ∀ σ : List (SupportProfile m n), IsSupportOrder σ →
      ∀ enum : SupportProfile m n → Finset (Fin m → Fin n → ℕ) → List (Fin m → Fin n → ℕ),
        IsFrontierEnum enum →
        ∃ x, (run u ε enum σ).out = some x ∧ IsEpsNash u ε x) ∧
    (∃ C : ℝ, 1 < C ∧ ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → ∀ M ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : Ω → Game m n), (∀ i s, Measurable fun ω => G ω i s) → (∀ ω, PayoffsIn01 (G ω)) →
        BoundedDensity P G M →
      ∀ σ : Game m n → List (SupportProfile m n), (∀ u, IsSupportOrder (σ u)) →
      ∀ enum : Game m n → SupportProfile m n → Finset (Fin m → Fin n → ℕ) →
          List (Fin m → Fin n → ℕ), (∀ u, IsFrontierEnum (enum u)) →
        ∫⁻ ω, ((run (G ω) ε (enum (G ω)) (σ (G ω))).evals : ℝ≥0∞) ∂P ≤
          ENNReal.ofReal ((1 + (D m ε : ℝ)) * (C * m * M) ^ (m * n))) ∧
    (∀ (κ : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ, 1 < C ∧
      ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → ∀ M ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : Ω → Game m n), (∀ i s, Measurable fun ω => G ω i s) → (∀ ω, PayoffsIn01 (G ω)) →
        BoundedDensity P G M →
      ∀ σ : Game m n → List (SupportProfile m n), (∀ u, IsSupportOrder (σ u)) →
      ∀ enum : Game m n → SupportProfile m n → Finset (Fin m → Fin n → ℕ) →
          List (Fin m → Fin n → ℕ), (∀ u, IsFrontierEnum (enum u)) →
      ∀ T : ℝ, c * m * n ≤ T →
        ∫⁻ ω, ENNReal.ofReal (runTime T κ (run (G ω) ε (enum (G ω)) (σ (G ω)))) ∂P ≤
          ENNReal.ofReal (T * (1 + (D m ε : ℝ)) * (C * m * M) ^ (m * n))) := by sorry

end SmoothedNash
