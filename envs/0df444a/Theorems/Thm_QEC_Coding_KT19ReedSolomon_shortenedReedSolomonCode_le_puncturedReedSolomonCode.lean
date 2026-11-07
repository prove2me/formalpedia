-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_le_puncturedReedSolomonCode
-- name    : QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_le_puncturedReedSolomonCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:57:29.03925+00:00
-- url     : https://prove2.me/theorems/f83c3d34-c571-41ea-80ce-a77e6fe57ff9
-- title:
--   KT19 Reed Solomon: shortened Reed Solomon Code le punctured Reed Solomon Code
-- statement:
--   The KT19 Reed Solomon construction uses the shortened Reed Solomon Code le punctured Reed Solomon Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L173-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L173-L180

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime

theorem QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_le_puncturedReedSolomonCode
    (p l k : Nat) [Fact p.Prime] :
    (shortenedReedSolomonCode p l k).carrier ≤
      (puncturedReedSolomonCode p l k).carrier := by sorry
