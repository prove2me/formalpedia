-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedComplementaryReedSolomon_minimumDistance
-- name    : QEC.Coding.KT19ReedSolomon.puncturedComplementaryReedSolomon_minimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:26.809512+00:00
-- url     : https://prove2.me/theorems/4dc8d888-abd5-4ad8-a67b-40e6921e2e6f
-- title:
--   KT19 Reed Solomon: punctured Complementary Reed Solomon minimum Distance
-- statement:
--   The complementary punctured Reed--Solomon code has its actual exact
--   distance.  The lower half counts polynomial roots; the upper half is the
--   explicit nodal product over retained locations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L632-L646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L632-L646

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime

theorem QEC.Coding.KT19ReedSolomon.puncturedComplementaryReedSolomon_minimumDistance
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistance (puncturedReedSolomonCode p (p - l) k) (l + 1 - k) := by sorry
