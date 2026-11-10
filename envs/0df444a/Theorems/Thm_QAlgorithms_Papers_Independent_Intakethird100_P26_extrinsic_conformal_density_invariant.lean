-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P26_extrinsic_conformal_density_invariant
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P26.extrinsic_conformal_density_invariant
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T05:03:18.156069+00:00
-- url     : https://prove2.me/theorems/e88724a7-e1ef-46c2-ba98-4e61f8cef9b9
-- title:
--   Conformal invariance of the two-surface extrinsic density
-- statement:
--   For a two-dimensional surface in a four-dimensional Riemannian manifold, let $\sigma$ be its positive definite induced metric matrix in tangent coordinates and let $k_i$ ($i=1,2$) be the two symmetric covariant second fundamental forms for orthonormal normals. Define
--
--   $$Q(\sigma,k)=\sum_{i=1}^2\left[(\operatorname{tr}(\sigma^{-1}k_i))^2-2\operatorname{tr}((\sigma^{-1}k_i)^2)\right].$$
--
--   For a Weyl factor $\omega$ and normal derivatives $v_i=n_i(\omega)$, use the source convention $\sigma^\prime=e^{-2\omega}\sigma$ and $k_i^\prime=e^{-\omega}(k_i+v_i\sigma)$. Then
--
--   $$\sqrt{\det\sigma^\prime}\,Q(\sigma^\prime,k^\prime)=\sqrt{\det\sigma}\,Q(\sigma,k).$$
--
--   This local density identity gives the conformal invariance of its integral over a smooth closed surface. It leaves the physical anomaly coefficient undetermined.
--
--   **Formalization Note** The assertion is the coordinate tensor identity at each point, valid for every positive definite metric and pair of symmetric covariant forms. It therefore needs no global tangent chart or normal frame. The bare scalar has weight +2; the plan’s density interpretation is used.
-- source:
--   Proof of the Holographic Formula for Entanglement Entropy, arXiv:hep-th/0606184v2, PDF p. 13, Section 4, after (4.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P26

noncomputable section

open Set

namespace QAlgorithms.Papers.Independent.Intakethird100.P26

/-- PDF p.13, after (4.5), with the second fundamental form convention
printed above (4.5). The invariant is the area-weighted density: the bare
scalar has conformal weight +2. This is a fibrewise tensor identity in local
coordinates, so it applies to every smooth closed embedded two-surface of
the source without a choice of a global coordinate chart or normal frame.
Its pointwise equality gives invariance of the integrated density.
Printed: the combination `(k^i)^2 - 2Tr(k^i k^i)` is conformally invariant.
Changed: assert invariance of its induced area-weighted density.
Why: the printed transformation gives the scalar weight +2, canceled exactly
by the two-dimensional area weight -2, as required by the integrated anomaly
argument. No change to (4.4) or determination of lambda is asserted. -/
theorem extrinsic_conformal_density_invariant
    (sigma : Matrix (Fin 2) (Fin 2) ℝ) (hsigma : sigma.PosDef)
    (k : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hk : ∀ i, (k i).IsSymm) (omega : ℝ) (v : Fin 2 → ℝ) :
    extrinsicDensity (weylSurfaceMetric omega sigma)
      (weylSecondForms omega v sigma k) = extrinsicDensity sigma k := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P26

end
