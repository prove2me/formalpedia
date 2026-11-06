-- Prove2me | Theorems.Thm_SemiBanditSOO_theorem_3_2
-- name    : SemiBanditSOO.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:45.498424+00:00
-- url     : https://prove2.me/theorems/a474d6aa-425b-4c87-9aea-cbeec7e345f1
-- title:
--   Theorem 3.2 — optimistic DP has regret $R_T\le c(\sqrt{ST\Lambda\log T(1+\log T)}+S\Lambda(1+\log T))+\delta T$
-- statement:
--   Consider stochastic online optimization over a decision tree with semi-bandit feedback, with independent coordinates $X_i\sim D_i$ on known domains $\mathrm{dom}(i)\subseteq[0,1]$. Under Assumption 3.1 with parameters $s_1,\dots,s_n\in\mathbb Z_{>0}\cup\{\infty\}$, let $k_i\in\mathbb Z_{>0}\cup\{\infty\}$ be the number of support points of $D_i$, and suppose that $S=\sum_{i=1}^n\min\{s_i,k_i\}$ is finite. There is a universal constant $c$ such that, for every $\delta\in(0,1)$, Algorithm 1 satisfies
--   $$R_T\le c\Bigl(\sqrt{ST\Lambda\log T(1+\log T)}+S\Lambda(1+\log T)\Bigr)+\delta T,\qquad \Lambda=\log\bigl(80n(T+1)^3/\delta\bigr). \qquad (3.6)$$
--   In particular, for $\delta=1/(T+1)$, $R_T=\widetilde O(\sqrt{ST})$.
--
--   The bound holds without any monotonicity of the problem in the distributions, and it adapts to the smaller of the level-set complexity and the support size of each coordinate.
--
--   **Formalization Note.** The constant $c$ is quantified first, before the number of coordinates, the domains, the problem, the distributions, the complexities, $T$ and $\delta$. The "in particular" sentence is the second clause of the statement, with the same $c$ and the logarithmic factor written out: for $\delta=1/(T+1)$, $R_T\le c\sqrt{ST}\,\Lambda(1+\log T)$. The paper's standing measurability assumptions (rewards and feasibility measurable, p.7; optimistic values measurable, p.10) are hypotheses.
--
--   Differences from the source:
--   - generalization: a finite rooted decision tree → a finite rooted DAG (every node reachable from the root, a height function strictly decreasing along edges); reason: footnote 1 (p.6) states that the analysis applies to such DAGs since obs(u) is a function of the node; a tree is an instance
--   - encoding: partial observation vectors x_obs(u) → full vectors x : (i : Fin n) → dom i, with feasibility, rewards and policies required to depend only on the coordinates in obs(u); reason: Lean convention; the same problems
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: OPT(D) = sup over (possibly randomized) policies → sup over measurable deterministic policies; reason: a randomized policy is a distribution over deterministic ones, so its value is an average of deterministic values and the supremum is the same
--   - encoding: ties in (3.5) broken in a fixed order → least maximizer for an arbitrary linear order on the node type (the statement holds for every order); reason: a fixed order is a linear order on the nodes
--   - encoding: Algorithm 1 run on T i.i.d. rounds X^1, …, X^T ∼ D, rounds t = 1, …, T → a deterministic function of ω = (X^1, …, X^T) under the product measure, rounds numbered 0, …, T − 1; reason: Algorithm 1 has no internal randomness; the same run
--   - generalization: Assumption 3.1 for all nonempty families 𝒫_1, …, 𝒫_n → Assumption 3.1 only for families whose optimistic DP is measurable (MeasurableDP); reason: a weaker hypothesis; the proof applies the assumption only to the confidence sets of Algorithm 1, whose DP is measurable by the paper's assumption (p.10), and it keeps every expectation a genuine integral
--   - generalization: the optimistic values are measurable in the samples and observations (p.10) → ḡ^t_u and h̄^t_(u,v) jointly measurable in the history ω and the observations, for t < T (StandingMeasurable); reason: a weaker hypothesis: the samples are measurable functions of the history, so the paper's assumption implies it; it holds automatically for finite domains
--   - encoding: s_i, k_i ∈ ℤ_{>0} ∪ {∞}, S = Σ_i min{s_i, k_i} finite → s_i, k_i, S ∈ ℕ∞ with 1 ≤ s_i, k_i = supportCount D_i, S ≠ ⊤, and S cast to ℝ; reason: Lean convention; the same values
--   - encoding: n random variables X_1, …, X_n → hypothesis 1 ≤ n; reason: Λ = log(80n(T + 1)³/δ) is defined only for n ≥ 1; n = 0 is not a problem of the paper
--   - encoding: T rounds → T : ℕ with 1 ≤ T; reason: the number of rounds is a positive integer
--   - reading: R_T = Õ(√(ST)) for δ = 1/(T + 1) → R_T ≤ c √(ST) Λ (1 + log T) for δ = 1/(T + 1), with the same universal c as (3.6); reason: Õ is not defined in the theorem; it hides factors polylogarithmic in n and T, and here Λ = log(80n(T + 1)⁴). The explicit factor is what (3.6) gives by the paper's argument (S ≤ √(ST) when T ≥ S, R_T ≤ T ≤ √(ST) when T < S)
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Theorem 3.2, (3.6), p.11

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP
import Definitions.Def_SemiBanditSOO_Algorithm

open MeasureTheory

namespace SemiBanditSOO

/-- **Theorem 3.2 (regret of optimistic DP).** Harada, Kawase, Sumita, *Beyond Monotonicity:
Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, Theorem 3.2, (3.6),
p.11.

Under Assumption 3.1, let `k_i ∈ ℤ_{>0} ∪ {∞}` be the number of support points of `D_i`, and
suppose that `S = Σ_{i=1}^n min{s_i, k_i}` is finite. There is a universal constant `c` such that,
for every `δ ∈ (0, 1)`, Algorithm 1 satisfies
`R_T ≤ c(√(S T Λ log T (1 + log T)) + S Λ (1 + log T)) + δ T`, with `Λ = log(80 n (T + 1)³ / δ)`.
In particular, for `δ = 1/(T + 1)`, we have `R_T = Õ(√(ST))`.

**Formalization Note.**
* `∃ c` is the outermost quantifier: `c` does not depend on `n`, the domains, the decision
  structure, the distributions, `s`, `T` or `δ`.
* The decision structure is a finite rooted DAG (footnote 1, p.6); trees are the special case.
* `s_i, k_i, S ∈ ℕ∞`; `S` is cast to `ℝ` after `S ≠ ⊤`.
* `1 ≤ n` makes `Λ` well defined; `1 ≤ T` is the number of rounds.
* `Õ(√(ST))` is stated with its logarithmic factor explicit: for `δ = 1/(T + 1)`,
  `R_T ≤ c √(ST) Λ (1 + log T)`, where `Λ = log(80 n (T + 1)⁴)`. The same `c` serves both clauses.
* The standing measurability assumptions are hypotheses: rewards and feasibility are measurable
  (fields of `Problem`, p.7), and the optimistic values are measurable (p.10,
  `StandingMeasurable`). Assumption 3.1 is required only for families with a measurable
  optimistic DP (`Assumption31`). -/
theorem theorem_3_2 :
    ∃ c : ℝ, ∀ (n : ℕ) (dom : Fin n → Set ℝ) (V : Type) [Fintype V] [LinearOrder V]
      (Pb : Problem n dom V) (D : ∀ i, ProbabilityMeasure (dom i)) (s : Fin n → ℕ∞)
      (T : ℕ) (δ : ℝ),
      1 ≤ n → (∀ i, 1 ≤ s i) → Pb.Assumption31 s → totalCpx s D ≠ ⊤ →
      1 ≤ T → 0 < δ → δ < 1 → Pb.StandingMeasurable T δ →
      Pb.regret D T δ ≤
        c * (Real.sqrt (((totalCpx s D).toNat : ℝ) * T * Lam n T δ * Real.log T *
              (1 + Real.log T)) +
            ((totalCpx s D).toNat : ℝ) * Lam n T δ * (1 + Real.log T)) + δ * T ∧
      (δ = 1 / ((T : ℝ) + 1) →
        Pb.regret D T δ ≤
          c * (Real.sqrt (((totalCpx s D).toNat : ℝ) * T) * (Lam n T δ * (1 + Real.log T)))) := by sorry

end SemiBanditSOO
