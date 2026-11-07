-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_fundamentalRepresentationAction_rankFour_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_rankFour_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:35.515246+00:00
-- url     : https://prove2.me/theorems/0cdfeec1-d262-444c-9d8d-2dd8a646a408
-- title:
--   Spherical Hecke: inner fundamental Representation Action rank Four one
-- statement:
--   The Spherical Hecke construction uses the inner fundamental Representation Action rank Four one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L414-L425
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L414-L425

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_rankFour_one
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 4) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 1 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 3 w) := by sorry
