-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:54.55213+00:00
-- url     : https://prove2.me/theorems/fb1a8437-37d1-4e9a-974c-b46ffa77fbd8
-- title:
--   Cartwright Steger: cartwright Steger Matrix Group le upper Unipotent Infinity Residue Subgroup
-- statement:
--   The full Cartwright--Steger matrix group satisfies the integral
--   upper-unipotent infinity-residue condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1595-L1603
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1595-L1603

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
    (P : BasePrime) (r : Rank) :
    CartwrightStegerMatrixGroup P r ≤
      UpperUnipotentInfinityResidueSubgroup P r := by sorry
