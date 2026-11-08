-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_zero
-- name    : QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:44:31.159242+00:00
-- url     : https://prove2.me/theorems/2068c980-45bf-45ab-90bd-e46a024eee8e
-- title:
--   Tanner Lifted Product: cayley Hecke Element zero
-- statement:
--   The Tanner Lifted Product construction uses the cayley Hecke Element zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L29-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L29-L31

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

theorem QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_zero (label : W → G) (p : ℂ) :
    cayleyHeckeElement label p 0 = 1 := by sorry
