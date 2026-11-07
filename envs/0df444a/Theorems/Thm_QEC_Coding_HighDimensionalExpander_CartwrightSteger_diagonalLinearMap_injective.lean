-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_diagonalLinearMap_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.diagonalLinearMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:32:13.43232+00:00
-- url     : https://prove2.me/theorems/df632e17-e1bd-4b3a-bd56-506fd6b8eacb
-- title:
--   Cartwright Steger: diagonal Linear Map injective
-- statement:
--   The Cartwright Steger construction uses the diagonal Linear Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L236-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L236-L242

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.diagonalLinearMap_injective
    {K : Type*} [Field K] (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (Matrix.diagonalLinearMap n K K) := by sorry
