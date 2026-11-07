-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_product_le_dual
-- name    : QEC.Coding.KT19ReedSolomon.reedSolomonCode_product_le_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:57:24.921576+00:00
-- url     : https://prove2.me/theorems/437257b1-0e9e-44ca-a57a-e29f93cddb63
-- title:
--   KT19 Reed Solomon: reed Solomon Code product le dual
-- statement:
--   The source-correct product condition implies that the product of the
--   degree-`< l` code lies in its exact Euclidean dual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L227-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L227-L238

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

theorem QEC.Coding.KT19ReedSolomon.reedSolomonCode_product_le_dual (p l : Nat) [Fact p.Prime]
    (hproduct : 3 * l ≤ p + 1) :
    (coordinatewiseProductCode (reedSolomonCode p l) (reedSolomonCode p l)).carrier ≤
      (reedSolomonCode p l).dual.carrier := by sorry
