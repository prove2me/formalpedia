-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_bot_7804e84e449b
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_bot_7804e84e449b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:41.948397+00:00
-- url     : https://prove2.me/theorems/b714ba6c-d198-4c62-8305-6329598b70a2
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient bot 7804e84e449b: P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient bot 7804e84e449b
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient bot 7804e84e449b construction uses the P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient bot 7804e84e449b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L48-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreeness
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
open MvPolynomial
universe u v w
open GroundTheory.Heights₂.Heights.GenericFreeness

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_bot_7804e84e449b {A : Type u} [CommRing A] [IsDomain A] (σ : Type*) :
    IsGenericallyFree A (MvPolynomial σ A ⧸ (⊥ : Ideal (MvPolynomial σ A))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«isGenericallyFree_quotient_bot» := P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_bot_7804e84e449b
