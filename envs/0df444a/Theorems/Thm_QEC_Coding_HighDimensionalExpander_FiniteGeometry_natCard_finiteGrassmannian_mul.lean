-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_finiteGrassmannian_mul
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_finiteGrassmannian_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:33.305405+00:00
-- url     : https://prove2.me/theorems/4dd80a22-f47a-43f2-9727-098aec8e9518
-- title:
--   Finite Geometry: nat Card finite Grassmannian mul
-- statement:
--   Double-count independent frames by the subspace that they span.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L114-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L114-L135

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_finiteGrassmannian_mul
    (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) (hr : r ≤ Module.finrank k V) :
    Nat.card (FiniteGrassmannian k V r) *
        (∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val)) =
      ∏ i : Fin r,
        (Fintype.card k ^ Module.finrank k V - Fintype.card k ^ i.val) := by sorry
