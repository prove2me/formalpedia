-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integratedHeckeAction_mem_kFixedSubmodule
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeAction_mem_kFixedSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:26:20.019738+00:00
-- url     : https://prove2.me/theorems/dcc33400-694b-4960-936d-e9b963fd2d1e
-- title:
--   Spherical Hecke: integrated Hecke Action mem k Fixed Submodule
-- statement:
--   A bi-`K`-invariant Hecke function sends every vector to the actual
--   `K`-fixed submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L275-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L275-L322

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.integratedHeckeAction_mem_kFixedSubmodule
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (f : HeckeFunction k d) (v : V) :
    integratedHeckeAction rho f v ∈ kFixedSubmodule rho := by sorry
