-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_eq_biUnion_quotientFiber
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalDoubleCoset_eq_biUnion_quotientFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:34:11.219522+00:00
-- url     : https://prove2.me/theorems/f00c141f-aa94-410e-bb81-4f65fba66954
-- title:
--   Spherical Hecke: fundamental Double Coset eq bi Union quotient Fiber
-- statement:
--   The Spherical Hecke construction uses the fundamental Double Coset eq bi Union quotient Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L573-L594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean#L573-L594

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalDoubleCoset_eq_biUnion_quotientFiber
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    fundamentalDoubleCoset k d r =
      ⋃ q ∈ fundamentalNeighborCosets k d r,
        (QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q} := by sorry
