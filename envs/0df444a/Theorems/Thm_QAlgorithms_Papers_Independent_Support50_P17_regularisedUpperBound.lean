-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_regularisedUpperBound
-- name    : QAlgorithms.Papers.Independent.Support50.P17.regularisedUpperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:04:19.048572+00:00
-- url     : https://prove2.me/theorems/855d6076-383e-4459-8b8a-dd32fe5b233e
-- title:
--   Sharp regularised relative entropy chain and explicit extremizers
-- statement:
--   Let $\rho,\sigma$ be density matrices on the same nonzero $d$-dimensional complex Hilbert space. Fix any positive normalization scalar $c_d$ at this dimension. Put $\alpha=\lambda_{\min}(\rho)$, $\beta=\lambda_{\min}(\sigma)$ and $T=\tfrac12\|\rho-\sigma\|_1$, and define $R(\rho\|\sigma)=c_dS(\rho+I\|\sigma+I)$. Then
--
--   $$
--   R(\rho\|\sigma)\le c_d\left[(\beta+1+T)\log\left(1+\frac{T}{\beta+1}\right)-(\alpha+1)\log\left(1+\frac{T}{\alpha+1}\right)\right]\le c_dT\log(1+T).
--   $$
--
--   For every $d\ge3$, every $c_d>0$ and every $t\in[0,1]$, the actual diagonal densities
--
--   $$
--   \rho=\operatorname{Diag}(1-t,t,0,0,\ldots),\qquad\sigma=\operatorname{Diag}(1-t,0,t,0,\ldots)
--   $$
--
--   have trace distance $T=t$ and satisfy $R(\rho\|\sigma)=c_dt\log(1+t)$. Both endpoints are included.
--
--   This retains the full inequality chain and sharpness for every allowed distance in every dimension at least three. The identity shifts are unnormalised and no formula for $c_d$ is guessed.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 9, Corollary 2: regularised entropy inequalities and sharpness (21)–(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF p.9, Corollary 2, (21)–(23): full inequality chain at arbitrary fixed
positive normalization c, followed by the source's exact diagonal sharpness pair
for every d≥3 and t∈[0,1], including endpoints and zero padding. -/
theorem regularisedUpperBound :
    (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
      (c : ℝ), 0 < c → ∀ rho sigma : Matrix I I ℂ,
      IsDensityMatrix rho → IsDensityMatrix sigma →
      let alpha := minEigenvalue rho
      let beta := minEigenvalue sigma
      let T := traceDistance rho sigma
      let bound := c * ((beta + 1 + T) * Real.log (1 + T / (beta + 1)) -
        (alpha + 1) * Real.log (1 + T / (alpha + 1)))
      regularisedRelativeEntropy c rho sigma ≤ (bound : EReal) ∧
        bound ≤ c * T * Real.log (1 + T)) ∧
    (∀ d : ℕ, 3 ≤ d → ∀ c : ℝ, 0 < c → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      let rho := regularisedRho d t
      let sigma := regularisedSigma d t
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧ traceDistance rho sigma = t ∧
        regularisedRelativeEntropy c rho sigma =
          ((c * t * Real.log (1 + t) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
