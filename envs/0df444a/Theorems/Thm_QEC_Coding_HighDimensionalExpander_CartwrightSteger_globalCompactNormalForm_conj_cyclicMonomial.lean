-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalCompactNormalForm_conj_cyclicMonomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalCompactNormalForm_conj_cyclicMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:05.998652+00:00
-- url     : https://prove2.me/theorems/eff73474-be44-4c1f-8f88-f80ff9f6dc04
-- title:
--   Cartwright Steger: global Compact Normal Form conj cyclic Monomial
-- statement:
--   The global compact normal form has exactly the same computed diagonal
--   block as its local building representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1651-L1722
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1651-L1722

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalCompactNormalForm_conj_cyclicMonomial
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j : ℕ) (c : ConstantExtension P r) (k : ℕ) :
    infinityConjugationLinearMap P r
        (globalCompactNormalForm P r u j)
        (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) =
      constantMatrix P r (compactConjugationDiagonalBlock P r u j k c) *
        cyclicGeneratorMatrix P r ^ k := by sorry
