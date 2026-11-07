-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeActionContinuousLinear_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeActionContinuousLinear_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:26:02.963989+00:00
-- url     : https://prove2.me/theorems/7245b527-a515-433b-95cf-faef364cdade
-- title:
--   Spherical Hecke: integrated Hecke Action Continuous Linear apply
-- statement:
--   The Spherical Hecke construction uses the integrated Hecke Action Continuous Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L207-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L207-L215

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeActionContinuousLinear_apply
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (f : HeckeFunction k d) (v : V) :
    integratedHeckeActionContinuousLinear rho hcontinuous hunitary f v =
      integratedHeckeAction rho f v := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeActionContinuousLinear_apply
