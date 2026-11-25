-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatPosPartLocal_isOpen_ne_zero_8867941ae2ad
-- name    : P2M_GroundTheory_Heights__Heights_RatPosPartLocal_isOpen_ne_zero_8867941ae2ad
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:44.954844+00:00
-- url     : https://prove2.me/theorems/f0e1b6e9-208e-4749-9dd3-1b0f607f9f8b
-- title:
--   P2 M Ground Theory Heights  Heights Rat Pos Part Local is Open ne zero 8867941ae2ad: P2 M Ground Theory Heights  Heights Rat Pos Part Local is Open ne zero 8867941ae2ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Pos Part Local is Open ne zero 8867941ae2ad construction uses the P2 M Ground Theory Heights  Heights Rat Pos Part Local is Open ne zero 8867941ae2ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatPosPartLocal.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatPosPartLocal.lean#L17-L18

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

theorem P2M_GroundTheory_Heights__Heights_RatPosPartLocal_isOpen_ne_zero_8867941ae2ad (q : MvPolynomial (Fin n) ℂ) : IsOpen {x : Fin n → ℂ | eval x q ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatPosPartLocal».«isOpen_ne_zero» := P2M_GroundTheory_Heights__Heights_RatPosPartLocal_isOpen_ne_zero_8867941ae2ad
