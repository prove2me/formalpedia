-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_action
-- name    : QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:45:38.400973+00:00
-- url     : https://prove2.me/theorems/a06087fe-0535-4264-b0cf-7c0c750dd0cb
-- title:
--   Tanner Lifted Product: cayley Hecke Element action
-- statement:
--   The regular action of the group-algebra Hecke element is the same
--   polynomial evaluated at Cayley adjacency.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L49-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L49-L62

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

theorem QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_action
    (label : W → G) (p : ℂ) (n : ℕ) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyHeckeElement label p n) =
      (lpsHeckePolynomial ℂ p n).eval₂
        (algebraMap ℂ (Module.End ℂ (G → ℂ)))
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum label)) := by sorry
