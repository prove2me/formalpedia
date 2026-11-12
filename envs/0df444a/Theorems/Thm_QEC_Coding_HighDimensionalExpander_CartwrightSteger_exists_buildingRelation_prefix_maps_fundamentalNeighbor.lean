-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_buildingRelation_prefix_maps_fundamentalNeighbor
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_buildingRelation_prefix_maps_fundamentalNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:02:14.653556+00:00
-- url     : https://prove2.me/theorems/6e83e964-5e24-4806-a7e4-baa78644651c
-- title:
--   Cartwright Steger: exists building Relation prefix maps fundamental Neighbor
-- statement:
--   The Cartwright Steger construction uses the exists building Relation prefix maps fundamental Neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L605-L680
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L605-L680

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingVertexDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_buildingRelation_prefix_maps_fundamentalNeighbor
    (P : BasePrime) (r : Rank) (color : Nat)
    (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1))
    (q : CartwrightStegerBuildingVertex P r)
    (hq : q ∈ fundamentalNeighborCosets
      (BaseField P) r.matrixRank color) :
    ∃ u ∈ buildingRelationTupleFinset P r,
      buildingLatticeVertexMap P r
        (buildingGeneratorPrefixProduct P r color u) = q := by sorry
