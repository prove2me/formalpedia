-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
-- name    : QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:10:24.049315+00:00
-- url     : https://prove2.me/theorems/891df1cd-a5d9-423b-ac61-6352abba5303
-- title:
--   KT19 Reed Solomon: mem reed Solomon Code
-- statement:
--   The KT19 Reed Solomon construction uses the mem reed Solomon Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L117-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L117-L122

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators

theorem QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode (p l : Nat) [Fact p.Prime]
    (word : Word (ZMod p) (ZMod p)) :
    word ∈ (reedSolomonCode p l).carrier ↔
      ∃ polynomial : Polynomial.degreeLT (ZMod p) l,
        evaluationLinearMap p l polynomial = word := by sorry
