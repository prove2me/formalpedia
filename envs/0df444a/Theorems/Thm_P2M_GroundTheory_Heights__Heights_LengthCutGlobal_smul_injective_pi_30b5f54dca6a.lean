-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_smul_injective_pi_30b5f54dca6a
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_smul_injective_pi_30b5f54dca6a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:16.986828+00:00
-- url     : https://prove2.me/theorems/65529db4-2285-414b-b203-417931e956ca
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global smul injective pi 30b5f54dca6a: P2 M Ground Theory Heights  Heights Length Cut Global smul injective pi 30b5f54dca6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global smul injective pi 30b5f54dca6a construction uses the P2 M Ground Theory Heights  Heights Length Cut Global smul injective pi 30b5f54dca6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L62-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
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
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_smul_injective_pi_30b5f54dca6a {y : C} (hy : y ∉ P) (n : ℕ) (v : Fin n → C ⧸ P) (h : y • v = 0) :
    v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«smul_injective_pi» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_smul_injective_pi_30b5f54dca6a
