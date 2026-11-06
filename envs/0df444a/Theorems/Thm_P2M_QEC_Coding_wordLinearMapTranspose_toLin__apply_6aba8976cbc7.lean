-- Prove2me | Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
-- name    : P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:04:09.533595+00:00
-- url     : https://prove2.me/theorems/b4e4a1c8-1b7e-4b12-aa70-95aab7eadf20
-- title:
--   P2 M QEC Coding word Linear Map Transpose to Lin  apply 6aba8976cbc7: P2 M QEC Coding word Linear Map Transpose to Lin  apply 6aba8976cbc7
-- statement:
--   Coordinate formula for transposing a matrix-defined word map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L60-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L60-L75

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
    {row col : Type v} [Fintype row] [Fintype col] [DecidableEq col]
    (M : Matrix row col F) (x : Word F row) (c : col) :
    wordLinearMapTranspose (Matrix.toLin' M) x c =
      ∑ r : row, x r * M r c := by sorry

alias «QEC».«Coding».«wordLinearMapTranspose_toLin'_apply» := P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
