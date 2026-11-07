-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicBasis_repr_eq_zero_of_mem_filtration
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_eq_zero_of_mem_filtration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:23.669116+00:00
-- url     : https://prove2.me/theorems/dbcc770e-d406-4ea4-bca5-1e86087f45d9
-- title:
--   Cartwright Steger: splitting Cyclic Basis repr eq zero of mem filtration
-- statement:
--   Blocks at or above the filtration bound have zero coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1195-L1225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1195-L1225

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_eq_zero_of_mem_filtration
    (P : BasePrime) (r : Rank) (bound : ℕ)
    (X : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hX : X ∈ InfinityCyclicFiltration P r bound)
    (p : Fin r.matrixRank × Fin r.matrixRank)
    (hp : bound ≤ (p.2 : ℕ)) :
    (splittingCyclicBasis P r).repr X p = 0 := by sorry
