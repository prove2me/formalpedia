-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_kt19_family_parameters
-- name    : QEC.Coding.KT19ReedSolomon.kt19_family_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:57:53.501802+00:00
-- url     : https://prove2.me/theorems/2aae7b13-6036-4e5b-bfd4-0da26bb119b0
-- title:
--   KT19 Reed Solomon: kt19 family parameters
-- statement:
--   The source-correct concrete family parameters.  The length and logical
--   dimension are computed from the retained coordinate type and actual shortened
--   code dimensions, while the safe distance is justified by the exact punctured
--   distance theorem above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L675-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L675-L689

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime

theorem QEC.Coding.KT19ReedSolomon.kt19_family_parameters (p l k : Nat) [Fact p.Prime]
    (h : Admissible p l k) :
    kt19Length p k = p - k ∧
      kt19LogicalDimension p l k = k ∧
        kt19SafeDistance p l k ≥ l - k := by sorry
