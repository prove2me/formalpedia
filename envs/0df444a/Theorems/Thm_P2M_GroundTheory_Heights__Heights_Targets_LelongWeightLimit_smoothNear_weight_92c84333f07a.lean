-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_smoothNear_weight_92c84333f07a
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_smoothNear_weight_92c84333f07a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:17.407015+00:00
-- url     : https://prove2.me/theorems/db4d8f3f-4672-5eae-ae22-51b2413edaef
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit smooth Near weight 92c84333f07a: P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit smooth Near weight 92c84333f07a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit smooth Near weight 92c84333f07a construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit smooth Near weight 92c84333f07a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L53-L64

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

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_smoothNear_weight_92c84333f07a {Z : Set (Fin n → ℂ)} (u : Fin n → ℂ) {k : (Fin n → ℂ) → ℝ}
    (hk : SmoothNear Z k) (hk0 : ∀ x ∈ Z, 0 < k x) {ε : ℝ} (hε : 0 < ε) :
    SmoothNear Z (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightLimit».«smoothNear_weight» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_smoothNear_weight_92c84333f07a
