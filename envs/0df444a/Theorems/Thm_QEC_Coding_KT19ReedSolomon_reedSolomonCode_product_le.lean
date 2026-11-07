-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_product_le
-- name    : QEC.Coding.KT19ReedSolomon.reedSolomonCode_product_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:11:22.280131+00:00
-- url     : https://prove2.me/theorems/7d330442-0b0b-4c5e-94e0-d97b287a16ac
-- title:
--   KT19 Reed Solomon: reed Solomon Code product le
-- statement:
--   The degree calculation gives containment of the actual product code in a
--   larger Reed--Solomon evaluation code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L158-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L158-L167

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

theorem QEC.Coding.KT19ReedSolomon.reedSolomonCode_product_le (p l m : Nat) [Fact p.Prime] :
    (coordinatewiseProductCode (reedSolomonCode p l) (reedSolomonCode p m)).carrier ≤
      (reedSolomonCode p (l + m - 1)).carrier := by sorry
