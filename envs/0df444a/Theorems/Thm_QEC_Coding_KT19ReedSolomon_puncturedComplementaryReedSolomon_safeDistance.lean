-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedComplementaryReedSolomon_safeDistance
-- name    : QEC.Coding.KT19ReedSolomon.puncturedComplementaryReedSolomon_safeDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:02.161682+00:00
-- url     : https://prove2.me/theorems/10566667-0d0a-4d67-a108-b89d205a4838
-- title:
--   KT19 Reed Solomon: punctured Complementary Reed Solomon safe Distance
-- statement:
--   The source-advertised `l-k` distance is exported only as a safe lower
--   bound; the preceding theorem retains the stronger exact `l+1-k` result.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L650-L656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L650-L656

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime

theorem QEC.Coding.KT19ReedSolomon.puncturedComplementaryReedSolomon_safeDistance
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistanceAtLeast (puncturedReedSolomonCode p (p - l) k) (l - k) := by sorry
