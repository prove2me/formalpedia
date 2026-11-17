-- Prove2me | Theorems.Thm_SemiBanditSOO_Supplement_theorem_3_6
-- name    : SemiBanditSOO.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:17:37.962145+00:00
-- url     : https://prove2.me/theorems/578459e8-789e-4156-b9b2-13a58d4ef853
-- title:
--   Theorem 3.6 — every learner has regret $\ge\frac1{64}\min\{T,\sqrt{ST}\}$ on some instance with full feedback and Assumption 3.1
-- statement:
--   For any integers $T\ge1$ and $s_1,\dots,s_n\ge1$, there is a problem with $n$ coordinates that has the following properties.
--
--   1. Every coordinate has a finite domain, and every leaf reward is $0$ or $1$. The learner receives full feedback: all $n$ coordinates are observed in every round under every policy.
--   2. Assumption 3.1 holds with $s_1,\dots,s_n$.
--   3. For every randomized learning algorithm there is a product distribution $D$, each $D_i$ with exactly $2s_i+1$ support points, such that
--   $$R_T(D)\ \ge\ \frac1{64}\min\bigl\{T,\sqrt{ST}\bigr\},\qquad S=s_1+\dots+s_n .$$
--
--   Together with Theorem 3.2, this shows that the worst-case regret over problems satisfying Assumption 3.1 with $s_1,\dots,s_n$ is $\widetilde\Theta(\min\{T,\sqrt{ST}\})$, even under full feedback.
--
--   **Formalization Note.** The problem depends only on $T$, $n$ and $s$; it is fixed before the learner, and $D$ is chosen after the learner and its randomness. Full feedback is stated as $\mathrm{obs}(\ell)=[n]$ at every leaf. Learners range over every probability space of internal randomness.
--
--   Differences from the source:
--
--   - generalization: learners choose σ^t from the observations X^τ_obs(ℓ^τ) of past rounds → learners may use the full past round vectors X^τ, τ < t; reason: every semi-bandit learner is such a learner, so the lower bound over the larger class implies the paper's; under the full feedback of (i) the two classes coincide
--   - reading: "randomized learning algorithm" and the expectation over its internal randomness → internal randomness ξ drawn once from a probability measure on an arbitrary measurable space Ξ : Type, the round-t choice jointly measurable in (ξ, history, current observations); reason: the expectation E[f(σ^t, X^t)] in R_T presupposes this measurability; fresh randomness per round and randomized policies within a round are the case of a product space
--   - generalization: all n coordinates are observed in every round under every policy → obs(ℓ) = [n] at every leaf; reason: a stronger conclusion: every policy ends at a leaf, so it implies the paper's (i); the paper's instance has it
--   - generalization: n coordinates (n ≥ 1 implicit in s_1, …, s_n) → every n : ℕ, including n = 0; reason: at n = 0, S = 0 and the bound is 0; for n ≥ 1 it is the paper's statement
--   - encoding: a problem (finite decision tree) → a published Problem on a finite node type (rooted DAG, Fintype V); reason: a finite rooted DAG unfolds into a tree with the same observations, feasible sets, rewards, policies and regret, so the existence claims are equivalent; it is the model of the published Theorem 3.2
--   - encoding: Assumption 3.1 for all nonempty families of distributions → the published Assumption31 (families whose optimistic DP is measurable); reason: on the finite domains of (i) every function of the observation vector is measurable, so every family qualifies and the two coincide
--   - encoding: product distribution D with D_i having 2s_i + 1 support points → D : ∀ i, ProbabilityMeasure (dom i) on the subtype dom i, supportCount (D i) = 2s_i + 1, rounds drawn from the product measure; reason: Lean convention; the same distributions
--   - encoding: OPT(D) = sup over (possibly randomized) policies → sup over measurable deterministic policies (published OPT); reason: a randomized policy's value is an average of deterministic values, so the supremum is the same
--   - encoding: rounds t = 1, …, T → rounds numbered 0, …, T − 1 (Fin T); reason: Lean convention; the same sum
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Theorem 3.6, p.12 (proof §6, pp.29–32)

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP
import Definitions.Def_SemiBanditSOO_Algorithm
import Definitions.Def_SemiBanditSOO_Supplement_Learner

open MeasureTheory

namespace SemiBanditSOO.Supplement

/-- **Theorem 3.6 (regret lower bound).** Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic
Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, Theorem 3.6, p.12 (proof §6,
pp.29–32).

For any integers `T ≥ 1` and `s_1, …, s_n ≥ 1`, there is a problem with `n` coordinates such that
(i) every coordinate has a finite domain, every leaf reward is `0` or `1`, and the learner receives
full feedback (all `n` coordinates are observed in every round under every policy);
(ii) Assumption 3.1 holds with `s_1, …, s_n`;
(iii) for every randomized learning algorithm there is a product distribution `D` with
`R_T(D) ≥ (1/64) min{T, √(ST)}`, where `S = s_1 + ⋯ + s_n`, and each `D_i` has `2 s_i + 1` support
points.

**Formalization Note.**
* Quantifier order: the problem depends on `T`, `n` and `s` only; it is chosen before the learner,
  and `D` after the learner (and its randomness space and measure).
* Full feedback is stated as `obs(ℓ) = [n]` at every leaf, so every policy observes every
  coordinate in every round.
* Assumption 3.1 is the published `Problem.Assumption31` (families with a measurable optimistic
  DP); on finite domains every function is measurable, so it is the paper's assumption.
* Learners range over every probability space `Ξ : Type` of internal randomness, and may use the
  full past round vectors (`Learner`); `R_T(D)` is `Learner.regret`.
* `n = 0` is allowed (then `S = 0` and the bound is `0`). -/
theorem theorem_3_6 (T n : ℕ) (s : Fin n → ℕ) (hT : 1 ≤ T) (hs : ∀ i, 1 ≤ s i) :
    ∃ (dom : Fin n → Set ℝ) (V : Type) (_ : Fintype V) (Pb : Problem n dom V),
      -- (i)
      ((∀ i, (dom i).Finite) ∧
        (∀ ℓ, Pb.children ℓ = ∅ → ∀ x, Pb.reward ℓ x = 0 ∨ Pb.reward ℓ x = 1) ∧
        (∀ ℓ, Pb.children ℓ = ∅ → Pb.obs ℓ = Finset.univ)) ∧
      -- (ii)
      Pb.Assumption31 (fun i => ((s i : ℕ) : ℕ∞)) ∧
      -- (iii)
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (L : Learner Pb T Ξ),
        ∃ D : ∀ i, ProbabilityMeasure (dom i),
          (∀ i, supportCount (D i : Measure (dom i)) = 2 * ((s i : ℕ) : ℕ∞) + 1) ∧
          (1 / 64 : ℝ) * min (T : ℝ) (Real.sqrt ((∑ i, (s i : ℝ)) * T)) ≤ L.regret μ D := by sorry

end SemiBanditSOO.Supplement
