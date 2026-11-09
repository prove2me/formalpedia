-- Prove2me | Theorems.Thm_RecGaussColoring_Main_fact_2_2
-- name    : RecGaussColoring.Main.fact_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:10.454539+00:00
-- url     : https://prove2.me/theorems/0f4a2913-ce1a-425f-a284-6ed9e9fb6950
-- title:
--   Fact 2.2 — Ehrhard inequality
-- statement:
--   Let $A,B$ be convex Borel subsets of $\mathbb R^d$ with Gaussian probabilities strictly between zero and one. For $0\le\theta\le1$, the Gaussian probability $\gamma_d$ satisfies
--   $$
--   \gamma_d(\theta A+(1-\theta)B)\ge
--   \Phi\bigl(\theta\Phi^{-1}(\gamma_d(A))+(1-\theta)\Phi^{-1}(\gamma_d(B))\bigr).
--   $$
--   This is Ehrhard's convex-set inequality, used by the lower-tail bound. Only the two interior probabilities enter the real inverse; a mixture of probability one is included.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
--   - encoding: inverse-CDF inequality, with +∞ permitted on the left → equivalent CDF inequality using real quantiles only at the interior probabilities; reason: strict monotonicity of Φ gives equivalence, including a full-measure Minkowski mixture; Gaussian measure of the mixture uses its outer-measure extension
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Fact 2.2, (2.1), p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Gaussian

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open Cohen2019.Robust
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Fact 2.2, p. 7, in the equivalent CDF form that includes a full-measure mixture. -/
theorem fact_2_2 (d : ℕ) (A B : Set (Space d))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAc : Convex ℝ A) (hBc : Convex ℝ B)
    (hAp : 0 < gaussProb A) (hA1 : gaussProb A < 1)
    (hBp : 0 < gaussProb B) (hB1 : gaussProb B < 1)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
  Phi (θ * PhiInvReal (gaussProb A) + (1-θ)*PhiInvReal (gaussProb B)) ≤
    gaussProb (minkowskiMix θ A B) := by sorry

end RecGaussColoring.Main
