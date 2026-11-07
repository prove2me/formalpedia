-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_conj_constantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_pow_conj_constantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:33.459633+00:00
-- url     : https://prove2.me/theorems/546ef987-8592-424f-9681-b38af31730e7
-- title:
--   Cartwright Steger: cyclic Generator pow conj constant Matrix
-- statement:
--   Conjugation by a natural power of the global cyclic unit is exactly the
--   corresponding Frobenius power on the represented constant field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1609-L1639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1609-L1639

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_pow_conj_constantMatrix
    (P : BasePrime) (r : Rank) (j : ℕ)
    (c : ConstantExtension P r) :
    ((cyclicGenerator P r ^ j :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) *
        constantMatrix P r c *
        (((cyclicGenerator P r ^ j)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) =
      constantMatrix P r ((constantFrobenius P r ^ j) c) := by sorry
