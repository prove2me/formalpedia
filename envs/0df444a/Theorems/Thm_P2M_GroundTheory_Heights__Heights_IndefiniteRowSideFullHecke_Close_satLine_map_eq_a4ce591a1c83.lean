-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_satLine_map_eq_a4ce591a1c83
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_satLine_map_eq_a4ce591a1c83
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:43.284016+00:00
-- url     : https://prove2.me/theorems/31171250-cbe6-4dc9-aa19-8701042b160e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sat Line map eq a4ce591a1c83: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sat Line map eq a4ce591a
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sat Line map eq a4ce591a1c83 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sat Line map eq a4ce591a1c83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L302-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L302-L317

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [NumberField K'] [Algebra K K']
  {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_satLine_map_eq_a4ce591a1c83 (v : Fin n → 𝓞 K') :
    (satLine v).map (intoField K' n) =
      stdLatticeExt K K' n ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ fun j ↦ (v j : K'))).restrictScalars (𝓞 K') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«satLine_map_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_satLine_map_eq_a4ce591a1c83
