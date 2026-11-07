-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_mem_filtration
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_mem_filtration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:30.386017+00:00
-- url     : https://prove2.me/theorems/499595ad-33d2-41da-8ab7-0d7e6470d0e3
-- title:
--   Cartwright Steger: infinity Conjugation Correction Sum mem filtration
-- statement:
--   The Cartwright Steger construction uses the infinity Conjugation Correction Sum mem filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1291-L1302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1291-L1302

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_mem_filtration
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (hbound : bound ≤ r.matrixRank)
    (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k bound ζ ∈
      InfinityCyclicFiltration P r bound := by sorry
