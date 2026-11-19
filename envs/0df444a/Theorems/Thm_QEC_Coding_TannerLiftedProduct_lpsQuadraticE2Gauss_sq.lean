-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Gauss_sq
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Gauss_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:28.847206+00:00
-- url     : https://prove2.me/theorems/9ba5442c-e61a-4f9b-ac02-d97bbe9038b4
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Gauss sq
-- statement:
--   The genuine standard quadratic Gauss sum has square equal to the residue prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L63-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L63-L69

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Gauss_sq (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))^2=(q:ℂ) := by sorry
