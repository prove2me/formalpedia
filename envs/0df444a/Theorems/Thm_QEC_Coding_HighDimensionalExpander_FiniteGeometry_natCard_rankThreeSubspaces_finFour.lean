-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_rankThreeSubspaces_finFour
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankThreeSubspaces_finFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:30.768484+00:00
-- url     : https://prove2.me/theorems/94f87734-3ff2-46e7-bd04-ec73c38829a0
-- title:
--   Finite Geometry: nat Card rank Three Subspaces fin Four
-- statement:
--   The Finite Geometry construction uses the nat Card rank Three Subspaces fin Four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L254-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L254-L305

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankThreeSubspaces_finFour
    (k : Type*) [Field k] [Fintype k] :
    Nat.card (FiniteGrassmannian k (Fin 4 → k) 3) =
      Fintype.card k ^ 3 + Fintype.card k ^ 2 + Fintype.card k + 1 := by sorry
