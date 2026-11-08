-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSGeneratorMatrixListMachine_generatorSL_decode
-- name    : QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.generatorSL_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:20:50.922209+00:00
-- url     : https://prove2.me/theorems/d254f272-11f9-4140-a9f6-b17765e2ed64
-- title:
--   LPSGenerator Matrix List Machine: generator SL decode
-- statement:
--   Actual finite instruction construction or proved invariant, whole execution, budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGeneratorMatrixListMachine.lean#L180-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGeneratorMatrixListMachine.lean#L180-L182

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

theorem QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.generatorSL_decode {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) :
    (QuotientGroup.mk (generatorSL a t):PSL(2,ZMod a.q))=lpsQuaternionLabel a t := by sorry
