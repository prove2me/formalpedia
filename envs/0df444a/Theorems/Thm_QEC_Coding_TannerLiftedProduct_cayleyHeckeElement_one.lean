-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_one
-- name    : QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:44:24.336605+00:00
-- url     : https://prove2.me/theorems/203847d0-eb20-49a2-af33-55c865a47822
-- title:
--   Tanner Lifted Product: cayley Hecke Element one
-- statement:
--   The Tanner Lifted Product construction uses the cayley Hecke Element one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L33-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L33-L35

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

theorem QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_one (label : W → G) (p : ℂ) :
    cayleyHeckeElement label p 1 = cayleyGeneratorSum label := by sorry
