-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_projectiveSpace_finFour
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_projectiveSpace_finFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:20:54.723721+00:00
-- url     : https://prove2.me/theorems/297c4ed9-b525-4591-936f-89e9d8d9c8bd
-- title:
--   Finite Geometry: nat Card projective Space fin Four
-- statement:
--   The Finite Geometry construction uses the nat Card projective Space fin Four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L316-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L316-L323

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_projectiveSpace_finFour
    (k : Type*) [Field k] [Finite k] :
    Nat.card (Projectivization k (Fin 4 → k)) =
      Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 := by sorry
