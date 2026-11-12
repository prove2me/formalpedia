-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_image_buildingColorGeneratorFinset_vertexMap
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_buildingColorGeneratorFinset_vertexMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:02:10.765592+00:00
-- url     : https://prove2.me/theorems/f70a0257-333e-45c8-820e-7e0f7be1276e
-- title:
--   Cartwright Steger: image building Color Generator Finset vertex Map
-- statement:
--   The Cartwright Steger construction uses the image building Color Generator Finset vertex Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L682-L704
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/PrefixHeckeCompatibility.lean#L682-L704

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingVertexDecidableEq

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_buildingColorGeneratorFinset_vertexMap
    (P : BasePrime) (r : Rank) (color : Nat)
    (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    (buildingColorGeneratorFinset P r color).image
        (buildingLatticeVertexMap P r) =
      fundamentalNeighborCosets (BaseField P) r.matrixRank color := by sorry
