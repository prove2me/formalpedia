-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_integratedHeckeAction_eq_star
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_integratedHeckeAction_eq_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:25:59.698134+00:00
-- url     : https://prove2.me/theorems/b7204e4a-efb7-422f-bcfc-906c34a8da6f
-- title:
--   Spherical Hecke: inner integrated Hecke Action eq star
-- statement:
--   Integration respects the proved Hecke involution: in every strongly
--   continuous unitary representation, the operator integrated from `star f` is
--   the Hilbert-space adjoint of the operator integrated from `f`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L220-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L220-L271

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_integratedHeckeAction_eq_star
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (hd : 0 < d) (f : HeckeFunction k d) (v w : V) :
    inner ℂ (integratedHeckeAction rho f v) w =
      inner ℂ v (integratedHeckeAction rho (star f) w) := by sorry
