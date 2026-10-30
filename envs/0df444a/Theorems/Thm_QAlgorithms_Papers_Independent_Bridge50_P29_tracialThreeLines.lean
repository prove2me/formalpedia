-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P29_tracialThreeLines
-- name    : QAlgorithms.Papers.Independent.Bridge50.P29.tracialThreeLines
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:31:21.232186+00:00
-- url     : https://prove2.me/theorems/5ad5c9ff-f40f-45bf-bf8d-bb1600293be7
-- title:
--   Hadamard three-lines inequality for semifinite tracial quasi-norms
-- statement:
--   Let $M$ be a von Neumann algebra with a normal semifinite faithful trace $\tau$, and let $G$ be a bounded operator-norm-continuous function from the closed strip into $M$, analytic in its interior. Let $0<p_0<p_1\leq\infty$ and $0\leq\theta\leq1$. Define $p_\theta$ by $1/p_\theta=(1-\theta)/p_0+\theta/p_1$, with $1/\infty=0$, and set $M_k=\sup_{t\in\mathbb R}\|G(k+it)\|_{p_k,\tau}$ for $k=0,1$. Then
--
--   $$
--   \|G(\theta)\|_{p_\theta,\tau}\leq M_0^{1-\theta}M_1^\theta.
--   $$
--
--   For finite $p>0$, the gauge is $(\tau(|x|^p))^{1/p}$, with value $+\infty$ when the trace is infinite; at $p=\infty$ it is the operator norm. Suprema and products use extended nonnegative values and the zeroth-power convention at the endpoints. No finite trace or trace normalization is required. This extends the three-lines inequality to tracial quasi-norms below one.
-- source:
--   Interpolation of quasi noncommutative $L_p$-spaces, arXiv:1905.08491v1, PDF p. 11, Proposition 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P29

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Bridge50.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Next46.P33
  (PositivePart Weight IsNormalWeight IsFaithfulWeight IsSemifiniteWeight positiveOne)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (extendedLog upperLogIntegral betaDensity betaZero interpolationExponent spectralFunction)

-- The frozen closedStrip is exactly the strip used in Section 2.4, PDF p.9.

open QAlgorithms.Papers.Independent.Support21.P21 (closedStrip)

section Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Proposition 3.4, arXiv:1905.08491v1, PDF pp.11--12.
No finite trace or normalization is added. ENNReal suprema preserve infinite
endpoint sizes. The reciprocal-affine exponent includes infinity, and the
theta=0,1 boundary cases use the standard zeroth-power convention. -/
theorem tracialThreeLines
    (M : VonNeumannAlgebra H) (tau : Weight M) (htrace : IsNSFTrace tau)
    (G : ℂ → (H →L[ℂ] H)) (hG : IsStripAnalytic G)
    (hGM : ∀ z ∈ closedStrip, G z ∈ M)
    (p0 p1 : ℝ≥0∞) (hp0 : 0 < p0) (hpp : p0 < p1)
    (theta : ℝ) (htheta : 0 ≤ theta ∧ theta ≤ 1) :
    tracialGauge tau (interpolationExponent theta p0 p1) (G (theta : ℂ)) ≤
      (tracialBoundarySup tau G p0 0) ^ (1 - theta) *
        (tracialBoundarySup tau G p1 1) ^ theta := by sorry

end Tracial

end QAlgorithms.Papers.Independent.Bridge50.P29

end
