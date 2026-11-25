-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_smul_eq_zero_16718e8e445b
-- name    : P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_smul_eq_zero_16718e8e445b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:25.901929+00:00
-- url     : https://prove2.me/theorems/ba63c02d-4232-4ad1-9dfc-ba85bfbfad7a
-- title:
--   P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of smul eq zero 16718e8e445b: P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of smul eq zero 16718e8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of smul eq zero 16718e8e445b construction uses the P2 M Ground Theory Heights  Heights Generic Freeness is Generically Free of smul eq zero 16718e8e445b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFreenessLoc.lean#L119-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
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
open GroundTheory.Heights₂.Heights.GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_smul_eq_zero_16718e8e445b {M : Type*} [AddCommGroup M] [Module A M] (a : A) (ha : a ≠ 0)
    (h : ∀ m : M, a • m = 0) : IsGenericallyFree A M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericFreeness».«isGenericallyFree_of_smul_eq_zero» := P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_smul_eq_zero_16718e8e445b
