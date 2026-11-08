-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyWordElement_add_one
-- name    : QEC.Coding.TannerLiftedProduct.cayleyWordElement_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:20:49.793291+00:00
-- url     : https://prove2.me/theorems/a048a533-8ac7-4afd-a479-fdd5a7f1f2e1
-- title:
--   Tanner Lifted Product: cayley Word Element add one
-- statement:
--   Prefixing one generator gives the exact word recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L65-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L65-L95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Mathlib.Data.Fintype.Vector
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v} [Group G] [Fintype W]

theorem QEC.Coding.TannerLiftedProduct.cayleyWordElement_add_one
    (label : W → G) (n : ℕ) :
    cayleyWordElement label (n + 1) =
      cayleyGeneratorSum label * cayleyWordElement label n := by sorry
