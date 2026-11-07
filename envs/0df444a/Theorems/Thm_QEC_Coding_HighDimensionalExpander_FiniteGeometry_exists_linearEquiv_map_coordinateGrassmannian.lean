-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_exists_linearEquiv_map_coordinateGrassmannian
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.exists_linearEquiv_map_coordinateGrassmannian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:46.844193+00:00
-- url     : https://prove2.me/theorems/9ef3b72e-a9ad-4a26-852d-a75c6c607950
-- title:
--   Finite Geometry: exists linear Equiv map coordinate Grassmannian
-- statement:
--   Any `r`-plane is the image of the standard coordinate plane under an
--   actual linear automorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L484-L506
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L484-L506

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.exists_linearEquiv_map_coordinateGrassmannian
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (W : FiniteGrassmannian k (Fin d → k) r) :
    ∃ g : (Fin d → k) ≃ₗ[k] (Fin d → k),
      (coordinateGrassmannian k d r hr).1.map g.toLinearMap = W.1 := by sorry
