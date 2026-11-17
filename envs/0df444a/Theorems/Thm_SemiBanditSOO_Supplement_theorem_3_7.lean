-- Prove2me | Theorems.Thm_SemiBanditSOO_Supplement_theorem_3_7
-- name    : SemiBanditSOO.Supplement.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:18:21.311384+00:00
-- url     : https://prove2.me/theorems/39e68825-1ae6-420f-a092-8c6df9a2aa0e
-- title:
--   Theorem 3.7 — with immediate rewards satisfying (a)–(c), Algorithm 1 satisfies (3.6) with $S=\sum_i s_i$ and a larger universal constant
-- statement:
--   Let $s_1,\dots,s_n\ge1$ be integers and $S=\sum_i s_i$. Suppose that each revelation edge $e=(u,v)$ has a measurable immediate reward $\chi_e(x_{\mathrm{obs}(v)})\in[0,1]$ satisfying conditions (a)–(c) of Theorem 3.7 (level-set complexity at most $s_i$ of $\chi_e$ in the revealed coordinate and the decomposition $f_\ell=\kappa_e+\chi_e+F_{e,\ell}$ with $0\le F_{e,\ell}\le1$; residual rewards and feasible sets nonincreasing in $x_i$; immediate rewards summing to at most $1$ along every feasible root-to-leaf path). Then there is a universal constant $c$ such that, for every $\delta\in(0,1)$, Algorithm 1 satisfies
--   $$R_T\le c\Bigl(\sqrt{ST\Lambda\log T(1+\log T)}+S\Lambda(1+\log T)\Bigr)+\delta T,\qquad \Lambda=\log\bigl(80n(T+1)^3/\delta\bigr).$$
--   In particular, for $\delta=1/(T+1)$, $R_T=\widetilde O(\sqrt{ST})$.
--
--   No Assumption 3.1 is required: the immediate reward and the residual continuation value are controlled separately, so their sum may have large level-set complexity.
--
--   **Formalization Note.** The constant $c$ is quantified first and is a new constant (the proof gives $c=834$). Algorithm 1, its regret, $\Lambda$ and the standing measurability assumption on the optimistic values are those of the published Theorem 3.2. The "in particular" sentence is the second clause, with the same $c$: for $\delta=1/(T+1)$, $R_T\le c\sqrt{ST}\,\Lambda(1+\log T)$.
--
--   Differences from the source:
--
--   - generalization: a finite rooted decision tree, "the subtree rooted at v" → a finite rooted DAG (the published Problem), the nodes reachable from v; reason: footnote 1 (p.6) states that the analysis applies to such DAGs; a tree is an instance, and its subtree is the set of nodes reachable from v
--   - encoding: partial observation vectors x_obs(u), χ_e(x_obs(v)) → full vectors, with χ u v required to depend only on the coordinates in obs(v); reason: Lean convention; the same functions
--   - encoding: κ_e(x_obs(u)), a function of the observations → a number chosen for each x with v ∈ 𝒜_u(x), before the leaf and the remaining values; reason: the conditions on κ depend on x only through x_obs(u), so such a choice is a function of x_obs(u)
--   - reading: (b) "nonincreasing in x_i, with other coordinates fixed" → for all y, y' agreeing with x on obs(u), equal off coordinate i, with y_i ≤ y'_i: F_{e,ℓ}(y') ≤ F_{e,ℓ}(y) at every leaf reachable from v and 𝒜_w(y') ⊆ 𝒜_w(y) at every node w reachable from v (v included); reason: the literal content of (b)
--   - encoding: a root-to-leaf path consisting of feasible actions → a list of nodes starting at the root, ending at a leaf, each consecutive pair a feasible action for x, summing χ over its revelation edges; reason: Lean convention; the same paths
--   - encoding: distributions on dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i; reason: as in the published Theorem 3.2; the same distributions
--   - encoding: OPT(D) over (possibly randomized) policies → over measurable deterministic policies; reason: as in the published Theorem 3.2; the supremum is the same
--   - encoding: ties in (3.5) broken in a fixed order → least maximizer for an arbitrary linear order on the node type; reason: as in the published Theorem 3.2
--   - encoding: Algorithm 1 run on T i.i.d. rounds, t = 1, …, T → a deterministic function of the T round vectors under the product measure, rounds 0, …, T − 1; reason: as in the published Theorem 3.2; the same run
--   - generalization: the optimistic values are measurable in the samples and observations (p.10) → the published StandingMeasurable (joint measurability in the history and the observations along the algorithm's own samples); reason: a weaker hypothesis implied by the paper's, as in the published Theorem 3.2
--   - encoding: integers s_i ≥ 1, S = Σ_i s_i → s : Fin n → ℕ with 1 ≤ s_i, S cast to ℝ; reason: Lean convention; the same values
--   - encoding: n random variables X_1, …, X_n → hypothesis 1 ≤ n; reason: Λ is defined only for n ≥ 1
--   - encoding: T rounds → T : ℕ with 1 ≤ T; reason: the number of rounds is a positive integer
--   - reading: "(3.6) with a larger universal constant c" → ∃ c : ℝ quantified before every other variable, a new constant not tied to Theorem 3.2's; reason: the literal reading of "universal constant"
--   - reading: R_T = Õ(√(ST)) for δ = 1/(T + 1) → R_T ≤ c √(ST) Λ (1 + log T) for δ = 1/(T + 1), with the same c; reason: as in the published Theorem 3.2; Õ hides factors polylogarithmic in n and T, and the explicit factor is what (3.6) gives
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Theorem 3.7, p.13 (proof §5.3, pp.28–29)

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP
import Definitions.Def_SemiBanditSOO_Algorithm
import Definitions.Def_SemiBanditSOO_Supplement_ImmediateRewards

open MeasureTheory

namespace SemiBanditSOO.Supplement

/-- **Theorem 3.7 (immediate rewards).** Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic
Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, Theorem 3.7, p.13 (proof §5.3,
pp.28–29).

Let `s_1, …, s_n ≥ 1` be integers and `S = Σ_i s_i`. Suppose that each revelation edge
`e = (u, v)` has a measurable immediate reward `χ_e(x_obs(v)) ∈ [0, 1]` satisfying conditions
(a)–(c) (`ImmediateRewardConditions`). Then, for every `δ ∈ (0, 1)`, Algorithm 1 satisfies (3.6)
with a larger universal constant `c`:
`R_T ≤ c(√(S T Λ log T (1 + log T)) + S Λ (1 + log T)) + δ T`, `Λ = log(80 n (T + 1)³ / δ)`.
In particular, for `δ = 1/(T + 1)`, we have `R_T = Õ(√(ST))`.

**Formalization Note.**
* `∃ c` is the outermost quantifier; `c` is a new constant (the proof gives `c = 834`).
* No Assumption 3.1 and no support condition: `S = Σ_i s_i` with integer `s_i ≥ 1`.
* Algorithm 1, its regret, `Λ` and the standing measurability assumption are the published
  `Problem.regret`, `Lam` and `Problem.StandingMeasurable`, exactly as in Theorem 3.2.
* `Õ(√(ST))` is stated with its logarithmic factor explicit, as in the published Theorem 3.2:
  for `δ = 1/(T + 1)`, `R_T ≤ c √(ST) Λ (1 + log T)`, with the same `c`.
* `1 ≤ n` makes `Λ` well defined; `1 ≤ T` is the number of rounds. -/
theorem theorem_3_7 :
    ∃ c : ℝ, ∀ (n : ℕ) (dom : Fin n → Set ℝ) (V : Type) [Fintype V] [LinearOrder V]
      (Pb : Problem n dom V) (D : ∀ i, ProbabilityMeasure (dom i)) (s : Fin n → ℕ)
      (χ : V → V → Obs dom → ℝ) (T : ℕ) (δ : ℝ),
      1 ≤ n → (∀ i, 1 ≤ s i) → ImmediateRewardConditions Pb s χ →
      1 ≤ T → 0 < δ → δ < 1 → Pb.StandingMeasurable T δ →
      Pb.regret D T δ ≤
        c * (Real.sqrt ((∑ i, (s i : ℝ)) * T * Lam n T δ * Real.log T * (1 + Real.log T)) +
            (∑ i, (s i : ℝ)) * Lam n T δ * (1 + Real.log T)) + δ * T ∧
      (δ = 1 / ((T : ℝ) + 1) →
        Pb.regret D T δ ≤
          c * (Real.sqrt ((∑ i, (s i : ℝ)) * T) * (Lam n T δ * (1 + Real.log T)))) := by sorry

end SemiBanditSOO.Supplement
