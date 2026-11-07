-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_projectiveSpace_finThree
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_projectiveSpace_finThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:20:54.078322+00:00
-- url     : https://prove2.me/theorems/b0a306c4-57d2-4060-ba29-df5943809364
-- title:
--   Finite Geometry: nat Card projective Space fin Three
-- statement:
--   The Finite Geometry construction uses the nat Card projective Space fin Three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L307-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L307-L314

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_projectiveSpace_finThree
    (k : Type*) [Field k] [Finite k] :
    Nat.card (Projectivization k (Fin 3 → k)) =
      Nat.card k ^ 2 + Nat.card k + 1 := by sorry
