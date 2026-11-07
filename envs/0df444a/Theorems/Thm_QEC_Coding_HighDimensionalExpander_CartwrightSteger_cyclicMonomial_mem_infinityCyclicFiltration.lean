-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicMonomial_mem_infinityCyclicFiltration
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicMonomial_mem_infinityCyclicFiltration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:05.512737+00:00
-- url     : https://prove2.me/theorems/25d4ec74-2755-4528-a714-3ddc9cab0f21
-- title:
--   Cartwright Steger: cyclic Monomial mem infinity Cyclic Filtration
-- statement:
--   The Cartwright Steger construction uses the cyclic Monomial mem infinity Cyclic Filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1139-L1145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1139-L1145

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicMonomial_mem_infinityCyclicFiltration
    (P : BasePrime) (r : Rank) (bound : ℕ)
    (c : ConstantExtension P r) (k : ℕ)
    (hkBound : k < bound) (hkRank : k < r.matrixRank) :
    constantMatrix P r c * cyclicGeneratorMatrix P r ^ k ∈
      InfinityCyclicFiltration P r bound := by sorry
