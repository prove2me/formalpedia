-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_comap_ne_bot_d935be84853d
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_comap_ne_bot_d935be84853d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:06.084491+00:00
-- url     : https://prove2.me/theorems/4390ffa4-b0f6-413d-9f44-80ed42b474e3
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of comap ne bot d935be84853d: P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of comap ne bot d935be84
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of comap ne bot d935be84853d construction uses the P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of comap ne bot d935be84853d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L38-L46

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_comap_ne_bot_d935be84853d {A : Type u} [CommRing A] {σ : Type*} (q : Ideal (MvPolynomial σ A))
    (h : q.comap (C : A →+* MvPolynomial σ A) ≠ ⊥) : IsGenericallyFree A (MvPolynomial σ A ⧸ q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«isGenericallyFree_of_comap_ne_bot» := P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_comap_ne_bot_d935be84853d
