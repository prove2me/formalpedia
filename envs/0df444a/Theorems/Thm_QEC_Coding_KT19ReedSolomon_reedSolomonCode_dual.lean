-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dual
-- name    : QEC.Coding.KT19ReedSolomon.reedSolomonCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:10:57.572137+00:00
-- url     : https://prove2.me/theorems/46eced69-a5a6-4217-8027-a7dfd193f97c
-- title:
--   KT19 Reed Solomon: reed Solomon Code dual
-- statement:
--   The Euclidean dual of the full-length degree-`< l` code is exactly the
--   degree-`< p-l` full-length Reed--Solomon code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L212-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L212-L223

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

theorem QEC.Coding.KT19ReedSolomon.reedSolomonCode_dual (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) :
    (reedSolomonCode p l).dual.carrier = (reedSolomonCode p (p - l)).carrier := by sorry
