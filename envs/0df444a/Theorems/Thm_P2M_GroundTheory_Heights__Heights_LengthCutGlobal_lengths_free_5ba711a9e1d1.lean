-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_free_5ba711a9e1d1
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_free_5ba711a9e1d1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:16.620447+00:00
-- url     : https://prove2.me/theorems/80221dad-9de7-4f41-b134-d58d7118a506
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global lengths free 5ba711a9e1d1: P2 M Ground Theory Heights  Heights Length Cut Global lengths free 5ba711a9e1d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global lengths free 5ba711a9e1d1 construction uses the P2 M Ground Theory Heights  Heights Length Cut Global lengths free 5ba711a9e1d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L143-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L143-L150

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

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_free_5ba711a9e1d1 {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) {n : ℕ}
    {X : Type*} [AddCommGroup X] [Module C X] (e : X ≃ₗ[C] (Fin n → C ⧸ P)) :
    Module.length C (QuotSMulTop y X) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«lengths_free» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_free_5ba711a9e1d1
