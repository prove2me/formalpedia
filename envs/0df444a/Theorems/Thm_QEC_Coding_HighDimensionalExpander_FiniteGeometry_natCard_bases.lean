-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_bases
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_bases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:34.761839+00:00
-- url     : https://prove2.me/theorems/3fdcc8df-780d-4ef7-b701-72916f358768
-- title:
--   Finite Geometry: nat Card bases
-- statement:
--   The Finite Geometry construction uses the nat Card bases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L105-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L105-L111

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_bases
    (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) (h : Module.finrank k V = r) :
    Nat.card (Basis (Fin r) k V) =
      ∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val) := by sorry
