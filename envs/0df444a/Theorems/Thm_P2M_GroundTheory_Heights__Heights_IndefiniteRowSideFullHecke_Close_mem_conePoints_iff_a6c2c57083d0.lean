-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_iff_a6c2c57083d0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_iff_a6c2c57083d0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:58.907599+00:00
-- url     : https://prove2.me/theorems/36642f64-b8d4-4b3f-9217-155830d5315f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone Points iff a6c2c57083d0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone Points iff
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone Points iff a6c2c57083d0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone Points iff a6c2c57083d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L186-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PointHeightDegreeHypotheses.lean#L186-L204

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_iff_a6c2c57083d0 (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (z : Cone (oneBlockSizes e r) ℂ) :
    z ∈ Heights.conePoints (Heights.oneBlockIdeal om) ℂ ↔
      coneToPairs z ∈ mcPts (mCoordIdeal (oneBlockPt om r)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«mem_conePoints_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_iff_a6c2c57083d0
