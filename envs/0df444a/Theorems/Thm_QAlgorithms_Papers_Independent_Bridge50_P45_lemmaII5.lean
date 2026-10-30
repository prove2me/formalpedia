-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_lemmaII5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.lemmaII5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:11:39.053307+00:00
-- url     : https://prove2.me/theorems/d3fffe4c-9632-438a-ad9a-d2aa9bec77c5
-- title:
--   Convexity of the reciprocal perspective
-- statement:
--   Let $J\subset(0,\infty)$ and $J'$ be real intervals, let $f:J\to\mathbb R$ be convex, and let $\varphi(t)=at+b$ map $J'$ into $J$. Assume $f$ is continuous on the range of $\varphi$. On every subinterval $K\subset J'$ where $\varphi(t)>0$ and $1/\varphi(t)\in J$, the function
--   $$t\longmapsto\varphi(t)f\!\left(\frac1{\varphi(t)}\right)$$
--   is convex.
--
--   This is the perspective transformation used for auxiliary functions.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 4, Lemma II.5 Let f : J → R be a convex function on some interval J ⊆(0, +∞). Then for any affine

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)

open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)

open QAlgorithms (spectralProjector)

/-- Lemma II.5, PDF pp.4-5. Both the printed affine range condition and the
reciprocal well-definedness conditions are explicit. -/
theorem lemmaII5 (J Jprime K : Set ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hJ : Convex ℝ J) (hpositive : J ⊆ Ioi 0) (hf : ConvexOn ℝ J f)
    (hJprime : Convex ℝ Jprime) (hphi : ∀ t ∈ Jprime, a*t+b ∈ J)
    (hK : Convex ℝ K) (hsub : K ⊆ Jprime)
    (hdefined : ∀ t ∈ K, 0 < a*t+b ∧ (a*t+b)⁻¹ ∈ J)
    (hcontinuous : ContinuousOn f ((fun t => a*t+b) '' Jprime)) :
    ConvexOn ℝ K (fun t => (a*t+b) * f ((a*t+b)⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
