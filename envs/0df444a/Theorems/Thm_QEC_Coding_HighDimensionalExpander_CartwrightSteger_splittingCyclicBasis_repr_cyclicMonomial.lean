-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicBasis_repr_cyclicMonomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_cyclicMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:31:37.129656+00:00
-- url     : https://prove2.me/theorems/03283327-6231-415e-8492-1ee800f2be44
-- title:
--   Cartwright Steger: splitting Cyclic Basis repr cyclic Monomial
-- statement:
--   Coordinates of an arbitrary constant cyclic monomial in the explicit
--   splitting-field basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L645-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L645-L701

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_cyclicMonomial
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : Fin r.matrixRank) (p : Fin r.matrixRank × Fin r.matrixRank) :
    (splittingCyclicBasis P r).repr
        (constantMatrix P r c * cyclicGeneratorMatrix P r ^ (k : ℕ)) p =
      if p.2 = k then
        algebraMap (BaseField P) (SplittingFunctionField P r)
          ((constantBasis P r).repr c p.1)
      else 0 := by sorry
