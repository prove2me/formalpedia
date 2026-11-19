-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_neg_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:11.608458+00:00
-- url     : https://prove2.me/theorems/286c1ca7-61fc-40f2-bc3b-6dd1e4c4c613
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Character neg one
-- statement:
--   A residue prime congruent to one modulo four has quadratic character one at minus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L54-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L54-L60

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_neg_one (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsQuadraticE2Character q (-1:ZMod q)=1 := by sorry
