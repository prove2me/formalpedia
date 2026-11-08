-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyHeckeElement
-- name    : QEC.Coding.TannerLiftedProduct.trace_cayleyHeckeElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:45:03.854833+00:00
-- url     : https://prove2.me/theorems/d9db93e3-8fd7-416c-bdec-0a8a9b9e9ea3
-- title:
--   Tanner Lifted Product: trace cayley Hecke Element
-- statement:
--   The trace of the `n`-th Cayley Hecke operator is group order times the
--   identity coefficient of the corresponding group-algebra element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L66-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L66-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.trace_cayleyHeckeElement
    (label : W → G) (p : ℂ) (n : ℕ) :
    LinearMap.trace ℂ (G → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyHeckeElement label p n)) =
      (Fintype.card G : ℂ) * (cayleyHeckeElement label p n).coeff 1 := by sorry
