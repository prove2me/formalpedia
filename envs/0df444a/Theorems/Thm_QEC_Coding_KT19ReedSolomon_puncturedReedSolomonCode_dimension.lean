-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedReedSolomonCode_dimension
-- name    : QEC.Coding.KT19ReedSolomon.puncturedReedSolomonCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:15.548193+00:00
-- url     : https://prove2.me/theorems/05bf2966-140f-49a7-9996-23a9257391cb
-- title:
--   KT19 Reed Solomon: punctured Reed Solomon Code dimension
-- statement:
--   Restricting to at least `l` retained locations does not decrease the
--   dimension of the degree-`< l` evaluation code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L390-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L390-L398

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime

theorem QEC.Coding.KT19ReedSolomon.puncturedReedSolomonCode_dimension (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (hlength : l ≤ p - k) :
    Dimension (puncturedReedSolomonCode p l k) = l := by sorry
