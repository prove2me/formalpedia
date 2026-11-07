-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_quotientFiber
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_quotientFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:22.721701+00:00
-- url     : https://prove2.me/theorems/30a0c113-eb1d-41a4-b5ba-4f3e897f1943
-- title:
--   Spherical Hecke: normalized Local Haar Measure quotient Fiber
-- statement:
--   The Spherical Hecke construction uses the normalized Local Haar Measure quotient Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L564-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L564-L571

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_quotientFiber
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    normalizedLocalHaarMeasure k d
        ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q}) = 1 := by sorry
