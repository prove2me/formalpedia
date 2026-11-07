-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_quotientFiber_eq_preimage_left_mul
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.quotientFiber_eq_preimage_left_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:32:50.975926+00:00
-- url     : https://prove2.me/theorems/4a6d80a3-a4da-4c4b-8d2e-eb620250455c
-- title:
--   Spherical Hecke: quotient Fiber eq preimage left mul
-- statement:
--   The Spherical Hecke construction uses the quotient Fiber eq preimage left mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L548-L562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L548-L562

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.quotientFiber_eq_preimage_left_mul
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    (QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q} =
      (fun x ↦ q.out⁻¹ * x) ⁻¹' (maximalCompact k d : Set (HeckeGroup k d)) := by sorry
