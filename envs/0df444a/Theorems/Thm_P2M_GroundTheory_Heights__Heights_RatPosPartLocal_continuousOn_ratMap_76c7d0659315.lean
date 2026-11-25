-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatPosPartLocal_continuousOn_ratMap_76c7d0659315
-- name    : P2M_GroundTheory_Heights__Heights_RatPosPartLocal_continuousOn_ratMap_76c7d0659315
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:15.961663+00:00
-- url     : https://prove2.me/theorems/bcab8741-b848-4cdc-8c31-482b80c5db1c
-- title:
--   P2 M Ground Theory Heights  Heights Rat Pos Part Local continuous On rat Map 76c7d0659315: P2 M Ground Theory Heights  Heights Rat Pos Part Local continuous On rat Map 76c7d0659315
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Pos Part Local continuous On rat Map 76c7d0659315 construction uses the P2 M Ground Theory Heights  Heights Rat Pos Part Local continuous On rat Map 76c7d0659315 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatPosPartLocal.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatPosPartLocal.lean#L20-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatPosPartLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatPosPartLocal
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatPosPartLocal_continuousOn_ratMap_76c7d0659315 (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatPosPartLocal».«continuousOn_ratMap» := P2M_GroundTheory_Heights__Heights_RatPosPartLocal_continuousOn_ratMap_76c7d0659315
