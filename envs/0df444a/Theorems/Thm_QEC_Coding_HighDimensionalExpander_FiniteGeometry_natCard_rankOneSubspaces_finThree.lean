-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_rankOneSubspaces_finThree
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankOneSubspaces_finThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:19.958388+00:00
-- url     : https://prove2.me/theorems/544230b5-33d9-4304-92aa-88fce5042e2d
-- title:
--   Finite Geometry: nat Card rank One Subspaces fin Three
-- statement:
--   The Finite Geometry construction uses the nat Card rank One Subspaces fin Three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L188-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L188-L202

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankOneSubspaces_finThree
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 3 → k) 1) =
      Fintype.card k ^ 2 + Fintype.card k + 1 := by sorry
