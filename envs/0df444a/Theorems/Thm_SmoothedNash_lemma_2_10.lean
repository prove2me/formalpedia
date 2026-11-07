-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_10
-- name    : SmoothedNash.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:53:46.136207+00:00
-- url     : https://prove2.me/theorems/a7b298fe-4bb6-4c03-b656-3b3e19578882
-- title:
--   Lemma 2.10 — $N_0(A) = 1$ and $E[N_t(A)] \le (CmM)^{mn}$ for $1 \le t \le D$
-- statement:
--   Let $G$ be a random game on a probability space $(\Omega, \mathcal F, P)$ with $m \ge 1$ players, $n \ge 1$ actions and measurable payoffs in $[0, 1]$, satisfying Assumption 1.18 with constant $M$, and let $\varepsilon \in (0, 1]$ and $D = \lceil \log_2(4m/\varepsilon) \rceil$. Fix a support profile $A = (A_1, \dots, A_m)$. Then $N_0(A) = |\{b_A\}| = 1$, and for every $1 \le t \le D$,
--   $$
--   \mathbb E\bigl[N_t(A)\bigr] \le (CmM)^{mn},
--   $$
--   where $N_t(A) = |F_t(A)|$ is the number of level-$t$ centers and $C > 1$ is a universal constant (the same for all $m$, $n$, $M$, $\varepsilon$, the random game, $A$ and $t$).
--
--   The bound is per support profile and per level; summing it over the at most $2^{mn}$ support profiles and the $D + 1$ levels gives Theorem 2.2.
--
--   Differences from the source:
--   - encoding: F_t(A) and N_t(A) := |F_t(A)|, the centers that would be tested if the algorithm continued after any earlier return (p.14) → frontier u A t, an order-free Finset of numerator vectors; reason: the frontier is a set, so it does not depend on the processing order; numerator vectors are in bijection with the grid points (Lemma 2.1)
--   - encoding: the expectation E[·] of a count → the lower Lebesgue integral ∫⁻ of the count, cast to ℝ≥0∞; reason: the count is a nonnegative random variable; ∫⁻ is its expectation
--   - encoding: a random (realized) game satisfying Assumption 1.18 → a probability space (Ω, P), a random game G with measurable payoffs in [0, 1] for every ω, and BoundedDensity P G M; reason: measurability is implicit in "random game"; the density bound is the equivalent measure inequality of BoundedDensity
--   - encoding: a game with m players, each with n actions (m, n ≥ 1 implicit) → hypotheses 1 ≤ m and 1 ≤ n; reason: a game has a player, and Δ_n is empty for n = 0
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.10, pp.18–19

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_PayoffsIn01
import Definitions.Def_SmoothedNash_BoundedDensity
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_D
import Definitions.Def_SmoothedNash_bary
import Definitions.Def_SmoothedNash_frontier
open MeasureTheory
open scoped ENNReal

namespace SmoothedNash

/-- **Lemma 2.10 (Expected number of tested centers at a fixed level)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.18–19). Fix a
support profile `A = (A_1, …, A_m)`. Then `N_0(A) = 1`, and for every `1 ≤ t ≤ D`,
`E[N_t(A)] ≤ (CmM)^{mn}`, where `N_t(A) := |F_t(A)|` and `C > 1` is a universal constant.

**Formalization Note** `C` is quantified before `m, n, M, ε`, the probability space, the random game,
`A` and `t`. `N_0(A) = |{b_A}| = 1`. The expectation is the lower Lebesgue integral of the count;
`(Ω, P)` is a probability space and `G` a random game with measurable payoffs in `[0, 1]` satisfying
Assumption 1.18. -/
theorem lemma_2_10 :
    ∃ C : ℝ, 1 < C ∧ ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → ∀ (M ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : Ω → Game m n), (∀ i s, Measurable fun ω => G ω i s) → (∀ ω, PayoffsIn01 (G ω)) →
        BoundedDensity P G M → ∀ A : SupportProfile m n,
          ({bary A} : Finset (Fin m → Fin n → ℝ)).card = 1 ∧
          ∀ t : ℕ, 1 ≤ t → t ≤ D m ε →
            ∫⁻ ω, ((frontier (G ω) A t).card : ℝ≥0∞) ∂P ≤
              ENNReal.ofReal ((C * m * M) ^ (m * n)) := by sorry

end SmoothedNash
