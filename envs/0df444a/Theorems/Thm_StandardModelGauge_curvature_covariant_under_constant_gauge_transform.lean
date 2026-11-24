-- Prove2me | Theorems.Thm_StandardModelGauge_curvature_covariant_under_constant_gauge_transform
-- name    : StandardModelGauge.curvature_covariant_under_constant_gauge_transform
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T03:43:59.85259+00:00
-- url     : https://prove2.me/theorems/debb7bcb-3edc-4e5f-987b-929777922c14
-- title:
--   Curvature Covariance Under Constant Conjugation
-- statement:
--   Let $n$ be any natural number, and let $A_\mu$ and $dA_{\mu\nu}$ be complex $n\times n$ matrices for four direction indices $\mu,\nu$. For a complex coupling $c$, define
--
--   $$
--   F_{\mu\nu}=dA_{\mu\nu}-dA_{\nu\mu}+c(A_\mu A_\nu-A_\nu A_\mu).
--   $$
--
--   Given matrices $U,V$ with $VU=I$, transform the connection and derivative data by $A^U_\mu=UA_\mu V$ and $(dA)^U_{\mu\nu}=U dA_{\mu\nu}V$. The curvature formed from these transformed data satisfies
--
--   $$
--   F^U_{\mu\nu}=UF_{\mu\nu}V
--   $$
--
--   for every ordered pair $\mu,\nu$. This states covariance under a spacetime-constant conjugation; the theorem does not assume $UV=I$ or include the derivative term for local transformations.
-- source:
--   J. A. Shifflett, “Standard Model Lagrangian (including neutrino mass terms),” equations (6) and (28)–(30), updated 2 February 2015; https://perma.cc/QDL7-VQZZ; original PDF https://einstein-schrodinger.com/Standard_Model.pdf.

import Definitions.Def_standardModelGaugeCurvature

namespace StandardModelGauge

/-- For an invertible constant matrix gauge transformation, the curvature
transforms by conjugation. This theorem formalizes the global, spacetime-constant
special case of the field-strength transformation laws in equations (28)–(30). -/
theorem curvature_covariant_under_constant_gauge_transform (n : ℕ)
    (A : Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (coupling : ℂ) (U V : Matrix (Fin n) (Fin n) ℂ)
    (hVU : V * U = 1) (μ ν : Fin 4) :
    standardModelGaugeCurvature n
        (standardModelConstantGaugeTransform n U V A)
        (standardModelConstantGaugeTransformDerivative n U V dA)
        coupling μ ν =
      U * standardModelGaugeCurvature n A dA coupling μ ν * V := by
  sorry

end StandardModelGauge
