-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSGeneratorMatrixListMachine_sourceDirections_complete
-- name    : QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.sourceDirections_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:30:28.563443+00:00
-- url     : https://prove2.me/theorems/f4482e16-8c5e-47ed-ac6e-fb9ca5b35845
-- title:
--   LPSGenerator Matrix List Machine: source Directions complete
-- statement:
--   Actual finite instruction construction or proved invariant, whole execution, budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGeneratorMatrixListMachine.lean#L195-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGeneratorMatrixListMachine.lean#L195-L198

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.sourceDirections_complete {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (t:LPSGeneratorIndex p) :
    t∈sourceDirections hp hp4 := by sorry
