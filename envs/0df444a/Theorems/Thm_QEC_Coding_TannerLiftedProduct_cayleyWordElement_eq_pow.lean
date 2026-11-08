-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyWordElement_eq_pow
-- name    : QEC.Coding.TannerLiftedProduct.cayleyWordElement_eq_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:21:43.239301+00:00
-- url     : https://prove2.me/theorems/e8092e43-797b-4a5d-bf44-fd43383e49ce
-- title:
--   Tanner Lifted Product: cayley Word Element eq pow
-- statement:
--   The finite word element is exactly the corresponding power of the
--   labelled Cayley generator sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L99-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L99-L107

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Mathlib.Data.Fintype.Vector
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v} [Group G] [Fintype W]

theorem QEC.Coding.TannerLiftedProduct.cayleyWordElement_eq_pow
    (label : W → G) (n : ℕ) :
    cayleyWordElement label n = cayleyGeneratorSum label ^ n := by sorry
