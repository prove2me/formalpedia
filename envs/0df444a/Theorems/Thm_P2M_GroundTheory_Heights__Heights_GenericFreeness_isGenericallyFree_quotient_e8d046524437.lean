-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_e8d046524437
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_e8d046524437
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:34.804369+00:00
-- url     : https://prove2.me/theorems/e47fe064-cffd-483b-a9ef-a649ca060de5
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient e8d046524437: P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient e8d046524437
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient e8d046524437 construction uses the P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free quotient e8d046524437 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L53-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreeness.lean#L53-L89

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

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_e8d046524437 (hNN : GenericNoetherNormalisation.Statement.{u}) (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (q : Ideal (MvPolynomial (Fin n) A)),
      q.IsPrime → IsGenericallyFree A (MvPolynomial (Fin n) A ⧸ q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«isGenericallyFree_quotient» := P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_e8d046524437
