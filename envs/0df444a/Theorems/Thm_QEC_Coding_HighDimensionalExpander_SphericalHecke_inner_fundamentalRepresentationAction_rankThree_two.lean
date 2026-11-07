-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_fundamentalRepresentationAction_rankThree_two
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_rankThree_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:38.177482+00:00
-- url     : https://prove2.me/theorems/44c46dcc-d79f-460a-87c8-f3aebbd62646
-- title:
--   Spherical Hecke: inner fundamental Representation Action rank Three two
-- statement:
--   The Spherical Hecke construction uses the inner fundamental Representation Action rank Three two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L401-L412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L401-L412

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_rankThree_two
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 3) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 2 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 1 w) := by sorry
