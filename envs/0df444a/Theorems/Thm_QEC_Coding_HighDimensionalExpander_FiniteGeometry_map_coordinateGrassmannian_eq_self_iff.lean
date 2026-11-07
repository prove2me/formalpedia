-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_map_coordinateGrassmannian_eq_self_iff
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.map_coordinateGrassmannian_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:31.153186+00:00
-- url     : https://prove2.me/theorems/f4984b3a-e81f-444f-8690-e6eaac7529d7
-- title:
--   Finite Geometry: map coordinate Grassmannian eq self iff
-- statement:
--   A finite general-linear matrix stabilizes the standard coordinate plane
--   exactly when its lower-left block vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L404-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L404-L443

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.map_coordinateGrassmannian_eq_self_iff
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) k) :
    (coordinateGrassmannian k d r hr).1.map
        (Matrix.GeneralLinearGroup.toLin g).val =
        (coordinateGrassmannian k d r hr).1 ↔
      ∀ i j : Fin d, r ≤ i.val → j.val < r → g i j = 0 := by sorry
