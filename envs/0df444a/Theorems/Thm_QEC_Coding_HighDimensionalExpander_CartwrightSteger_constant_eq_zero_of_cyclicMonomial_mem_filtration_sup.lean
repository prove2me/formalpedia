-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constant_eq_zero_of_cyclicMonomial_mem_filtration_sup
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constant_eq_zero_of_cyclicMonomial_mem_filtration_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:23.020014+00:00
-- url     : https://prove2.me/theorems/65d3f46d-8cb0-48db-91cf-7261666fe9d5
-- title:
--   Cartwright Steger: constant eq zero of cyclic Monomial mem filtration sup
-- statement:
--   A pure degree-`k` constant block cannot lie in earlier blocks plus
--   `t L` unless its coefficient vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1229-L1289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1229-L1289

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constant_eq_zero_of_cyclicMonomial_mem_filtration_sup
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : Fin r.matrixRank)
    (hmem : constantMatrix P r c * cyclicGeneratorMatrix P r ^ (k : ℕ) ∈
      InfinityCyclicFiltration P r (k : ℕ) ⊔
        InfinityUniformizerMultiple P r) :
    c = 0 := by sorry
