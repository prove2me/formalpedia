-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_clearedImage_smith_normal_form
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_clearedImage_smith_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:03:51.200323+00:00
-- url     : https://prove2.me/theorems/2cf5e9fe-5eab-4303-acba-2faf8f264139
-- title:
--   Spherical Hecke: exists cleared Image smith normal form
-- statement:
--   Smith normal form applied to the construction-owned image lattice.  The
--   two bases and every diagonal coefficient are produced by the theorem; the
--   only rank premise is discharged by `clearedImage_finrank`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L272-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L272-L283

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_clearedImage_smith_normal_form
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ∃ (ambientBasis : Basis (Fin d) (IntegerRing k) (Fin d → IntegerRing k))
      (diagonalCoeff : Fin d → IntegerRing k)
      (imageBasis : Basis (Fin d) (IntegerRing k)
        (clearedImage (k := k) (d := d) A)),
      ∀ i, (imageBasis i : Fin d → IntegerRing k) =
        diagonalCoeff i • ambientBasis i := by sorry
