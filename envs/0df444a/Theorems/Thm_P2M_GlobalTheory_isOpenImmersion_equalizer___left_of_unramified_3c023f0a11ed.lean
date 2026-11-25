-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___left_of_unramified_3c023f0a11ed
-- name    : P2M_GlobalTheory_isOpenImmersion_equalizer___left_of_unramified_3c023f0a11ed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:45.449218+00:00
-- url     : https://prove2.me/theorems/2c200534-c8f9-48f9-934b-290764e3f221
-- title:
--   P2 M Global Theory is Open Immersion equalizer   left of unramified 3c023f0a11ed: P2 M Global Theory is Open Immersion equalizer   left of unramified 3c023f0a11ed
-- statement:
--   The P2 M Global Theory is Open Immersion equalizer   left of unramified 3c023f0a11ed construction uses the P2 M Global Theory is Open Immersion equalizer   left of unramified 3c023f0a11ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L47-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
set_option backward.isDefEq.respectTransparency false

theorem P2M_GlobalTheory_isOpenImmersion_equalizer___left_of_unramified_3c023f0a11ed {S : Scheme.{u}} {T X : Over S}
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] (a b : T ⟶ X) :
    IsOpenImmersion (equalizer.ι a b).left := by sorry

alias «GlobalTheory».«isOpenImmersion_equalizer_ι_left_of_unramified» := P2M_GlobalTheory_isOpenImmersion_equalizer___left_of_unramified_3c023f0a11ed
