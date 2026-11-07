-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationFormula_mem_lattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationFormula_mem_lattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:32:59.92571+00:00
-- url     : https://prove2.me/theorems/96b64ac7-2f7d-481b-8629-1a3b3c649ba5
-- title:
--   Cartwright Steger: infinity Conjugation Formula mem lattice
-- statement:
--   The Cartwright Steger construction uses the infinity Conjugation Formula mem lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L879-L894
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L879-L894

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationFormula_mem_lattice
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (hk : k < r.matrixRank) (ζ : ConstantExtension P r) :
    infinityConjugationFormula P r u k ζ ∈
      InfinityCyclicLattice P r := by sorry
