-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeries_integer_local_triangle
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeries_integer_local_triangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:52.750209+00:00
-- url     : https://prove2.me/theorems/c459c4bd-bb71-466f-9ba6-3a317b35882e
-- title:
--   Spherical Hecke: power Series integer local triangle
-- statement:
--   The Spherical Hecke construction uses the power Series integer local triangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L669-L677
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L669-L677

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeries_integer_local_triangle
    {k : Type u} [Field k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    integralGeneralLinearToLocal k d
        (powerSeriesGeneralLinearToInteger k d g) =
      powerSeriesGeneralLinearToLocal k d g := by sorry
