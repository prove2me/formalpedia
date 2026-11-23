-- Prove2me | Theorems.Thm_StochSQP_Vanishing_Supplement_lemma_24
-- name    : StochSQP.Vanishing.Supplement.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:22:46.999813+00:00
-- url     : https://prove2.me/theorems/f6e056a6-55de-4abb-8c4e-aec27a235fde
-- title:
--   Lemma 24 (used in the proof of Theorem 5) — finite-horizon exponential opportunity tail (corrected: s_max is the printed integer ceiling)
-- statement:
--   On the stochastic Algorithm 1 model with Assumptions 1 and 2, the pathwise part of Assumption 3, and all of Assumption 6, let $E$ be the true-trial lower-bound event, $p_\tau\in(0,1]$ the uniform conditional decrease probability, and $s_{\max}\in\mathbb Z$ the printed ceiling in (36). For every finite horizon $K\in\mathbb N$ and integer $J>s_{\max}/p_\tau+1$,
--   $$\mu\left(\sum_{k=0}^K I[T_k^{\mathrm{trial,true}}<T_k]\ge J\ \middle|\ E\right)\le\exp\left[-\frac{p_\tau(J-1)}2\left(1-\frac{s_{\max}}{p_\tau(J-1)}\right)^2\right].$$
--   This counts comparisons with the current merit, not the previous-merit indicators $Q_k$. The bound is uniform in $K$ and supports Theorem 5.
--
--   Differences from the source:
--   - reading: display (52) omits conditioning on E → conditional probability given E; reason: the final inequality in its proof on p. 40 explicitly conditions on E, and Definition 2 with Assumption 6 makes E certain
--   - correction: (36) annotates the ceiling as an element of ℕ → s_max is the printed ceiling as an integer; reason: the ceiling is negative when t>tau_-1/(1-eps_tau); there every T_k ≤ tau_-1 < t ≤ T_k^trial,true, so no opportunity occurs and (52) holds as printed; clamping at zero would weaken the bound
--   - generalization: Assumption 3's clause that H_k is chosen independently from g_k (conditionally on reaching x_k) → no independence condition between H_k and g_k; reason: the proofs of Lemmas 22–24 and Theorem 5 (pp. 33–40) use only Assumption 6, (44) and the monotonicity of the merit parameter; every source model satisfies the remaining hypotheses, so the statement specializes to the source's
--   - encoding: realized stochastic algorithm quantities and conditional probabilities → arbitrary probability spaces, measurable causal paths, event-integral conditional moments, and Mathlib conditional laws on reachable nodes; reason: these preserve adaptive distributions and the full probability model; null conditioning nodes do not affect the almost-sure assertion
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 39, Lemma 24

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Stochastic

namespace StochSQP.Vanishing.Supplement

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

theorem lemma_24
    {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Problem n m) (A : Params) (M : Process Ω n m)
    (X : Set (E n)) (κH ζH t pτ : ℝ)
    (hmodel : StochasticModel P A M μ X κH ζH)
    (h6 : Assumption6 P A M μ t pτ)
    (K J : ℕ) (hJ : (sMax A t : ℝ) / pτ + 1 < (J : ℝ)) :
    (cond μ (lowerEvent P A M t)) {ω | J ≤ opportunityCount P A M K ω} ≤
      ENNReal.ofReal (Real.exp (-pτ * ((J : ℝ) - 1) / 2 *
        (1 - (sMax A t : ℝ) / (pτ * ((J : ℝ) - 1))) ^ 2)) := by sorry

end StochSQP.Vanishing.Supplement
