-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_mem_lattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_mem_lattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:31:48.943649+00:00
-- url     : https://prove2.me/theorems/aee91110-c89f-4841-b7a5-cad382badb11
-- title:
--   Cartwright Steger: infinity Conjugation Correction Sum mem lattice
-- statement:
--   The Cartwright Steger construction uses the infinity Conjugation Correction Sum mem lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L866-L877
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L866-L877

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_mem_lattice
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (hbound : bound ≤ r.matrixRank)
    (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k bound ζ ∈
      InfinityCyclicLattice P r := by sorry
