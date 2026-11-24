-- Prove2me | Theorems.Thm_StandardModelGauge_gauge_kinetic_density_invariant_under_constant_gauge_transform
-- name    : StandardModelGauge.gauge_kinetic_density_invariant_under_constant_gauge_transform
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T03:44:27.742448+00:00
-- url     : https://prove2.me/theorems/4d375786-9438-4ac3-b33f-ae4ad9bd11fd
-- title:
--   Invariance of the Weighted Gauge Kinetic Density
-- statement:
--   Let $n$ be any natural number. Let $A_\mu$ and $dA_{\mu\nu}$ be complex $n\times n$ matrices, $c\in\mathbb C$ a coupling, and $w_{\mu\nu}\in\mathbb C$ arbitrary fixed weights. Define the curvature and weighted trace density by
--
--   $$
--   F_{\mu\nu}=dA_{\mu\nu}-dA_{\nu\mu}+c(A_\mu A_\nu-A_\nu A_\mu),
--   \qquad
--   K(A,dA;c,w)=\sum_{\mu,\nu}w_{\mu\nu}\,\operatorname{tr}(F_{\mu\nu}F_{\mu\nu}).
--   $$
--
--   If matrices $U,V$ satisfy $UV=VU=I$, then under $A_\mu\mapsto UA_\mu V$ and $dA_{\mu\nu}\mapsto U dA_{\mu\nu}V$, the density is unchanged:
--
--   $$
--   K(A^U,(dA)^U;c,w)=K(A,dA;c,w).
--   $$
--
--   The same ordered indices occur in both factors of each trace. The arbitrary weights permit fixed index contractions and normalizations; this is an algebraic constant-gauge result, not the full local Standard Model Lagrangian.
-- source:
--   J. A. Shifflett, “Standard Model Lagrangian (including neutrino mass terms),” equations (6) and (28)–(30), updated 2 February 2015; https://perma.cc/QDL7-VQZZ; original PDF https://einstein-schrodinger.com/Standard_Model.pdf.

import Definitions.Def_standardModelGaugeCurvature

namespace StandardModelGauge

/-- The weighted trace kinetic density is invariant under a constant gauge
transformation. The statement applies to any matrix size `n`, hence to the
source's SU(2) and SU(3) adjoint fields, once the required group elements are
viewed as invertible matrices. -/
theorem gauge_kinetic_density_invariant_under_constant_gauge_transform (n : ℕ)
    (A : Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (coupling : ℂ) (weight : Fin 4 → Fin 4 → ℂ)
    (U V : Matrix (Fin n) (Fin n) ℂ)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    standardModelGaugeKineticDensity n
        (standardModelConstantGaugeTransform n U V A)
        (standardModelConstantGaugeTransformDerivative n U V dA)
        coupling weight =
      standardModelGaugeKineticDensity n A dA coupling weight := by
  sorry

end StandardModelGauge
