-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_4d3ce82ed86f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_4d3ce82ed86f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:10.529462+00:00
-- url     : https://prove2.me/theorems/3abad917-1621-5c47-b8c3-9e2ff0b66138
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Ideal eq comap 4d3ce82ed86f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Ideal
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Ideal eq comap 4d3ce82ed86f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Ideal eq comap 4d3ce82ed86f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L155-L160

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
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_4d3ce82ed86f (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    Heights.oneBlockIdeal (r := r) om =
      (mCoordIdeal (oneBlockPt om r)).comap (rename (oneBlockReindex e r)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«oneBlockIdeal_eq_comap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_4d3ce82ed86f
