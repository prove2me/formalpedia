-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_theorem_5
-- name    : StochSQP.Vanishing.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:24:05.097521+00:00
-- url     : https://prove2.me/theorems/32bf5b30-9e85-4a29-865b-968be5aa91cd
-- title:
--   Theorem 5 (companion theorem; not used in the proof of the goal) — conditional almost-surely finite opportunities
-- statement:
--   On the stochastic Algorithm 1 model with Assumptions 1 and 2, the pathwise part of Assumption 3, and all of Assumption 6, let $E$ be the event from Definition 2 that the true trial merit stays above its specified positive lower bound. Then
--   $$\mu\left(\sum_{k=0}^{\infty}I[T_k^{\mathrm{trial,true}}<T_k]<\infty\ \middle|\ E\right)=1.$$
--   Equivalently, conditionally on $E$, the set of indices satisfying $T_k^{\mathrm{trial,true}}<T_k$ is finite almost surely. Assumption 6 includes the uniform decrease-probability bound on every reachable signature, constant curvature and ratio sequences, and the positive true-trial bound in every realization. No finite-opportunity assertion is assumed. This is the formal companion theorem corresponding to the informal Theorem 4.
--
--   Differences from the source:
--   - encoding: the infinite sum of nonnegative indicators is finite → the set of opportunity indices is finite; reason: these are equivalent for zero-one terms and the set formulation avoids the default value of a divergent real tsum
--   - encoding: conditional probability on E and adaptive stochastic algorithm quantities → Mathlib conditional measure on E, arbitrary probability spaces and measurable causal paths satisfying Assumptions 1–3; reason: the all-realizations lower bound makes E certain; no extra positive-probability premise or independence of successive gradients or opportunity indicators is imposed
--   - generalization: Assumption 3's clause that H_k is chosen independently from g_k (conditionally on reaching x_k) → no independence condition between H_k and g_k; reason: the proofs of Lemmas 22–24 and Theorem 5 (pp. 33–40) use only Assumption 6, (44) and the monotonicity of the merit parameter; every source model satisfies the remaining hypotheses, so the statement specializes to the source's
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 40, Theorem 5

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Stochastic

namespace StochSQP.Vanishing.Supplement

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

theorem theorem_5
    {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n m) (A : Params) (M : Process Ω n m)
    (X : Set (E n)) (κH ζH t pτ : ℝ)
    (hmodel : StochasticModel P A M μ X κH ζH)
    (h6 : Assumption6 P A M μ t pτ)
    : (cond μ (lowerEvent P A M t)) (finiteOpportunities P A M) = 1 := by sorry

end StochSQP.Vanishing.Supplement
