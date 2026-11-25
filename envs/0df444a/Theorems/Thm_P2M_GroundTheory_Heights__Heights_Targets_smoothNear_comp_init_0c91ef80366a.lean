-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_smoothNear_comp_init_0c91ef80366a
-- name    : P2M_GroundTheory_Heights__Heights_Targets_smoothNear_comp_init_0c91ef80366a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:40.932351+00:00
-- url     : https://prove2.me/theorems/421f619e-ace5-5e69-9e1d-5e13203b4e9e
-- title:
--   P2 M Ground Theory Heights  Heights Targets smooth Near comp init 0c91ef80366a: P2 M Ground Theory Heights  Heights Targets smooth Near comp init 0c91ef80366a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets smooth Near comp init 0c91ef80366a construction uses the P2 M Ground Theory Heights  Heights Targets smooth Near comp init 0c91ef80366a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongPolyLimit.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongPolyLimit.lean#L17-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongPolyLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StVarIntGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLocalMultComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongPolyLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b

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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

theorem P2M_GroundTheory_Heights__Heights_Targets_smoothNear_comp_init_0c91ef80366a {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {g : (Fin n → ℂ) → ℝ} (hg : SmoothNear (zeroSet J) g) :
    SmoothNear (zeroSet (graphIdeal J p)) (fun x => g (Fin.init x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«smoothNear_comp_init» := P2M_GroundTheory_Heights__Heights_Targets_smoothNear_comp_init_0c91ef80366a
