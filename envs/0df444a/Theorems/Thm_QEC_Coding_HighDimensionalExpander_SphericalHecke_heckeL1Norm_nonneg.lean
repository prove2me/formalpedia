-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_heckeL1Norm_nonneg
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.heckeL1Norm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:17.281003+00:00
-- url     : https://prove2.me/theorems/e56a2c68-5d69-48d1-8799-c893b84ceaba
-- title:
--   Spherical Hecke: hecke L1 Norm nonneg
-- statement:
--   The Spherical Hecke construction uses the hecke L1 Norm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L172-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L172-L175

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory
open scoped ComplexConjugate MatrixGroups LocalTopology
universe u v

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.heckeL1Norm_nonneg
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : 0 ≤ heckeL1Norm f := by sorry
