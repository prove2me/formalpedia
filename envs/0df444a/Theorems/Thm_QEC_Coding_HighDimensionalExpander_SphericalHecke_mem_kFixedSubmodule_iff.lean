-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mem_kFixedSubmodule_iff
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.mem_kFixedSubmodule_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:26:00.964061+00:00
-- url     : https://prove2.me/theorems/710dfb94-7732-4249-b54f-b884b5253e71
-- title:
--   Spherical Hecke: mem k Fixed Submodule iff
-- statement:
--   The Spherical Hecke construction uses the mem k Fixed Submodule iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L42-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean#L42-L48

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.mem_kFixedSubmodule_iff
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) (v : V) :
    v ∈ kFixedSubmodule rho ↔
      ∀ h : maximalCompact k d, rho h v = v := by sorry
