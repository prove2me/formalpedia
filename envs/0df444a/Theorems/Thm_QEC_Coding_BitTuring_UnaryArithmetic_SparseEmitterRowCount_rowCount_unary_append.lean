-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SparseEmitterRowCount_rowCount_unary_append
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount.rowCount_unary_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:09:24.530322+00:00
-- url     : https://prove2.me/theorems/105a61e9-92de-447f-a795-6b2dae3772ef
-- title:
--   Sparse Emitter Row Count: row Count unary append
-- statement:
--   The Sparse Emitter Row Count construction uses the row Count unary append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySparseEmitterArithmetic.lean#L143-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySparseEmitterArithmetic.lean#L143-L146

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnarySparseEmitterArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
open QEC.Coding.BitTuring Turing StateTransition FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount.rowCount_unary_append (k:Fin 4) (n:ℕ) (w:List Bool):rowCount k (unary n++w)=rowCount k w:= by sorry
