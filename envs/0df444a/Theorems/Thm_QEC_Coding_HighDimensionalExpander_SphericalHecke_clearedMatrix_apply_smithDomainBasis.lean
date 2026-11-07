-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedMatrix_apply_smithDomainBasis
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_apply_smithDomainBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:05.113264+00:00
-- url     : https://prove2.me/theorems/54918073-d7e0-4848-821c-a457facb6b7e
-- title:
--   Spherical Hecke: cleared Matrix apply smith Domain Basis
-- statement:
--   Coordinate-free Smith diagonalization of the cleared matrix: it maps the
--   constructed domain basis vector to the corresponding nonzero scalar multiple
--   of the constructed ambient basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L343-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L343-L358

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_apply_smithDomainBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) :
    Matrix.mulVec
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)))
        (smithDomainBasis (k := k) (d := d) A i) =
      smithDiagonalCoeff (k := k) (d := d) A i •
        smithAmbientBasis (k := k) (d := d) A i := by sorry
