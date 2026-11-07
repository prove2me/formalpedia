-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeAction_eq_eigenvalue_smul
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeAction_eq_eigenvalue_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:54:48.736604+00:00
-- url     : https://prove2.me/theorems/8f321fea-8517-4a2a-972f-182c30130613
-- title:
--   Spherical Hecke: integrated Hecke Action eq eigenvalue smul
-- statement:
--   If the actual `K`-fixed subspace is one-dimensional, every integrated
--   spherical Hecke operator acts on a unit `K`-fixed vector by the scalar just
--   constructed from the inner product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L466-L494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L466-L494

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeAction_eq_eigenvalue_smul
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (hline : Module.finrank ℂ (kFixedSubmodule rho) = 1)
    (f : HeckeFunction k d) (v : V)
    (hvfixed : v ∈ kFixedSubmodule rho) (hvnorm : ‖v‖ = 1) :
    integratedHeckeActionLinear rho hcontinuous f v =
      sphericalHeckeEigenvalue rho hcontinuous f v • v := by sorry
