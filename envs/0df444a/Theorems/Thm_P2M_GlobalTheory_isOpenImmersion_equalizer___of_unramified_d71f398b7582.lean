-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582
-- name    : P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:57.141622+00:00
-- url     : https://prove2.me/theorems/15dc70bd-cde0-4d41-9ad3-0d1d545b6466
-- title:
--   P2 M Global Theory is Open Immersion equalizer   of unramified d71f398b7582: P2 M Global Theory is Open Immersion equalizer   of unramified d71f398b7582
-- statement:
--   The P2 M Global Theory is Open Immersion equalizer   of unramified d71f398b7582 construction uses the P2 M Global Theory is Open Immersion equalizer   of unramified d71f398b7582 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L33-L37

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

theorem P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582 {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f) :
    IsOpenImmersion (equalizer.ι a b) := by sorry

alias «GlobalTheory».«isOpenImmersion_equalizer_ι_of_unramified» := P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582
