-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_cayleyGeneratorSum_pow
-- name    : QEC.Coding.TannerLiftedProduct.coeff_cayleyGeneratorSum_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:21:15.140227+00:00
-- url     : https://prove2.me/theorems/b023e9c0-8ba5-47f4-bc9b-871e61c53ccf
-- title:
--   Tanner Lifted Product: coeff cayley Generator Sum pow
-- statement:
--   A coefficient of an adjacency power counts labelled words with the given
--   group product, including parallel-label multiplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L111-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleyWordTrace.lean#L111-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Mathlib.Data.Fintype.Vector
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v} [Group G] [Fintype W]

theorem QEC.Coding.TannerLiftedProduct.coeff_cayleyGeneratorSum_pow
    [DecidableEq G] (label : W → G) (n : ℕ) (g : G) :
    (cayleyGeneratorSum label ^ n).coeff g =
      ((Finset.univ.filter fun word : List.Vector W n =>
        cayleyVectorWordProduct label word = g).card : ℂ) := by sorry
