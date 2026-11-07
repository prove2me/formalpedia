-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projective_eq_localCartanFactors
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projective_eq_localCartanFactors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:41.764048+00:00
-- url     : https://prove2.me/theorems/9e8761b8-fc47-4365-9d38-2727a0ab928c
-- title:
--   Spherical Hecke: projective eq local Cartan Factors
-- statement:
--   Projective Cartan equality.  The denominator-clearing scalar disappears
--   because scalar matrices are killed by `GL_d → PGL_d`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L704-L716
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L704-L716

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projective_eq_localCartanFactors
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk
          (smithLeftGeneralLinearLocal (k := k) (d := d) A) *
        smithPowerCoweight (k := k) (d := d) A *
      (Matrix.ProjGenLinGroup.mk
        (smithRightGeneralLinearLocal (k := k) (d := d) A))⁻¹ := by sorry
