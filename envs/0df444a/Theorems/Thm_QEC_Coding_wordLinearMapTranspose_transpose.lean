-- Prove2me | Theorems.Thm_QEC_Coding_wordLinearMapTranspose_transpose
-- name    : QEC.Coding.wordLinearMapTranspose_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:03:18.230486+00:00
-- url     : https://prove2.me/theorems/804a4d27-27ba-4616-adf4-ee153c7eb2bb
-- title:
--   Coding: word Linear Map Transpose transpose
-- statement:
--   Transposing a finite-coordinate linear map twice gives the original map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L20-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L20-L48

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.wordLinearMapTranspose_transpose
    (f : Word F i0 →ₗ[F] Word F i1) :
    wordLinearMapTranspose (wordLinearMapTranspose f) = f := by sorry
