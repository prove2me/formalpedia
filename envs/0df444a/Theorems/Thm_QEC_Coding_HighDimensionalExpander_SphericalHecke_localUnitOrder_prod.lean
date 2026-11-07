-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_prod
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:51.313713+00:00
-- url     : https://prove2.me/theorems/b4d80c62-91c4-48cc-b44f-22b8cfa04ec9
-- title:
--   Spherical Hecke: local Unit Order prod
-- statement:
--   The Spherical Hecke construction uses the local Unit Order prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1725-L1734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1725-L1734

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_prod
    {k : Type u} [Field k] {α : Type*}
    (s : Finset α) (f : α → Units (LocalFunctionField k)) :
    localUnitOrder (∏ i ∈ s, f i) =
      ∑ i ∈ s, localUnitOrder (f i) := by sorry
