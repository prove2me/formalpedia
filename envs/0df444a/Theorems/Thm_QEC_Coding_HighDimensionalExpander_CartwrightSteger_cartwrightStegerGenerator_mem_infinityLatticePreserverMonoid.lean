-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_mem_infinityLatticePreserverMonoid
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_mem_infinityLatticePreserverMonoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:34:11.684556+00:00
-- url     : https://prove2.me/theorems/45b35a24-b9ec-40dd-bb57-b25451aebb84
-- title:
--   Cartwright Steger: cartwright Steger Generator mem infinity Lattice Preserver Monoid
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Generator mem infinity Lattice Preserver Monoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1121-L1125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1121-L1125

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_mem_infinityLatticePreserverMonoid
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    cartwrightStegerGenerator P r x ∈
      InfinityLatticePreserverMonoid P r := by sorry
