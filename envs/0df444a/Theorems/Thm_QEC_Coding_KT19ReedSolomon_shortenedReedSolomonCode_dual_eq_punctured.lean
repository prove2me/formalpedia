-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dual_eq_punctured
-- name    : QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_dual_eq_punctured
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:57:36.664502+00:00
-- url     : https://prove2.me/theorems/c6f8532f-e44a-4a42-9f5d-23be652afbe0
-- title:
--   KT19 Reed Solomon: shortened Reed Solomon Code dual eq punctured
-- statement:
--   Complementary shortening/puncturing duality for the source's actual
--   coordinate partition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L431-L448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L431-L448

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime

theorem QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_dual_eq_punctured (p l k : Nat) [Fact p.Prime]
    (h : Admissible p l k) :
    (shortenedReedSolomonCode p (p - l) k).dual.carrier =
      (puncturedReedSolomonCode p l k).carrier := by sorry
