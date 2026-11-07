-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_compactNormalForm_hasIdentityDiagonal_of_mem_matrixGroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactNormalForm_hasIdentityDiagonal_of_mem_matrixGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:34:33.768674+00:00
-- url     : https://prove2.me/theorems/bb6938fa-2675-4f8a-b112-0b8af2f54cff
-- title:
--   Cartwright Steger: compact Normal Form has Identity Diagonal of mem matrix Group
-- statement:
--   Any compact normal form which is actually an element of the constructed
--   Cartwright--Steger matrix group has identity infinity diagonal blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1757-L1765
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1757-L1765

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactNormalForm_hasIdentityDiagonal_of_mem_matrixGroup
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j : ℕ)
    (hmem : globalCompactNormalForm P r u j ∈
      CartwrightStegerMatrixGroup P r) :
    CompactNormalFormHasIdentityDiagonal P r u j := by sorry
