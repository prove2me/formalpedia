-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_fundamentalRepresentationAction_eq_of_star
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_eq_of_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:25:56.539206+00:00
-- url     : https://prove2.me/theorems/c92ef3d0-9ffe-4a4d-809a-fafeb544b103
-- title:
--   Spherical Hecke: inner fundamental Representation Action eq of star
-- statement:
--   A concrete involution identity for fundamental Hecke functions becomes
--   the corresponding Hilbert-space adjoint identity for their represented
--   operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L366-L386
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L366-L386

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.inner_fundamentalRepresentationAction_eq_of_star
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (hd : 0 < d) (r s : ℕ)
    (hstar : star (HeckeFunction.fundamentalHeckeFunction k d r) =
      HeckeFunction.fundamentalHeckeFunction k d s)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous r v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous s w) := by sorry
