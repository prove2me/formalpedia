-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEPermutationAction_apply
-- name    : QEC.Coding.f256MFEPermutationAction_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:55.06992+00:00
-- url     : https://prove2.me/theorems/635e4891-48d4-41d1-ad36-5ec882effbf3
-- title:
--   Coding: f256 MFEPermutation Action apply
-- statement:
--   Evaluation of a reindexing action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L99-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean#L99-L101

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256MFEPermutationAction_apply (pi : Equiv.Perm (Fin 512))
    (v : Fin 512 → ZMod 2) (q : Fin 512) :
    f256MFEPermutationAction pi v q = v (pi q) := by sorry
