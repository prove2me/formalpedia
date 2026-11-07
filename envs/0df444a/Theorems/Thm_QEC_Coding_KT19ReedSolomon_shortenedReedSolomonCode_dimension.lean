-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dimension
-- name    : QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:16:09.803388+00:00
-- url     : https://prove2.me/theorems/eea40911-a0c9-4f87-88a5-d43ed67e57e6
-- title:
--   KT19 Reed Solomon: shortened Reed Solomon Code dimension
-- statement:
--   The dimension of the actual shortened code, obtained by selected-value
--   interpolation, rank-nullity, and injective restriction to retained points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L323-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean#L323-L355

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime

theorem QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_dimension (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (hkl : k ≤ l) (hlp : l ≤ p) :
    Dimension (shortenedReedSolomonCode p l k) = l - k := by sorry
