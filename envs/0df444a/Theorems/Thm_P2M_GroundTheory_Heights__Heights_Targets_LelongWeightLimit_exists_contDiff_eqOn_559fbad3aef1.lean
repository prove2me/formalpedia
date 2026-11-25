-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_exists_contDiff_eqOn_559fbad3aef1
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_exists_contDiff_eqOn_559fbad3aef1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:10.126546+00:00
-- url     : https://prove2.me/theorems/7fad807a-6c61-5efe-93cc-ea4fe59bf143
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit exists cont Diff eq On 559fbad3aef1: P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit exists cont Diff eq On 559fbad3aef1
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit exists cont Diff eq On 559fbad3aef1 construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit exists cont Diff eq On 559fbad3aef1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L20-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)
open GroundTheory.Heights₂.Heights.Targets.LelongWeightLimit
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_exists_contDiff_eqOn_559fbad3aef1 {Z : Set (Fin n → ℂ)} (hZ : IsClosed Z) {f : (Fin n → ℂ) → ℝ}
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightLimit».«exists_contDiff_eqOn» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_exists_contDiff_eqOn_559fbad3aef1
