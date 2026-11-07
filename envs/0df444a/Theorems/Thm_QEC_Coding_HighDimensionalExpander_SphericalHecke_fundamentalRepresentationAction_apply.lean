-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalRepresentationAction_apply
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalRepresentationAction_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:36.636118+00:00
-- url     : https://prove2.me/theorems/0e1249f6-79be-4fde-b076-909c3c70e06a
-- title:
--   Spherical Hecke: fundamental Representation Action apply
-- statement:
--   The fundamental action is the integral over the actual Cartan double
--   coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L336-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L336-L361

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalRepresentationAction_apply
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (r : ℕ) (v : V) :
    fundamentalRepresentationAction rho hcontinuous r v =
      ∫ g in fundamentalDoubleCoset k d r, rho g v
        ∂(normalizedLocalHaarMeasure k d) := by sorry
