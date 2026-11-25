-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_pi_c243c288e059
-- name    : P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_pi_c243c288e059
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:33.84315+00:00
-- url     : https://prove2.me/theorems/7eb8bd2f-1d2e-477f-bd7e-887f6c1d941b
-- title:
--   P2 M Ground Theory Heights  Heights Length Cut Global lengths pi c243c288e059: P2 M Ground Theory Heights  Heights Length Cut Global lengths pi c243c288e059
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Cut Global lengths pi c243c288e059 construction uses the P2 M Ground Theory Heights  Heights Length Cut Global lengths pi c243c288e059 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L113-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthCutGlobal.lean#L113-L141

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

theorem P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_pi_c243c288e059 {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) (n : ℕ) :
    Module.length C (QuotSMulTop y (Fin n → C ⧸ P)) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (Fin n → C ⧸ P)) = n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthCutGlobal».«lengths_pi» := P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_pi_c243c288e059
