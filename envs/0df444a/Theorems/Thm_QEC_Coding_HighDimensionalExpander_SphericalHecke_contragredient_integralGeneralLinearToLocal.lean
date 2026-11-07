-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_contragredient_integralGeneralLinearToLocal
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.contragredient_integralGeneralLinearToLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:02.259484+00:00
-- url     : https://prove2.me/theorems/fe6ae652-611b-440d-9707-5fb83a71b60e
-- title:
--   Spherical Hecke: contragredient integral General Linear To Local
-- statement:
--   The Spherical Hecke construction uses the contragredient integral General Linear To Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1321-L1333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1321-L1333

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.contragredient_integralGeneralLinearToLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    contragredientGeneralLinearHom (integralGeneralLinearToLocal k d A) =
      integralGeneralLinearToLocal k d
        (contragredientGeneralLinearHom A) := by sorry
