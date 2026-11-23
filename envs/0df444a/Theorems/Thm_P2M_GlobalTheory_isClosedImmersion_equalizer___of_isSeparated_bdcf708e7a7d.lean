-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
-- name    : P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:13.382698+00:00
-- url     : https://prove2.me/theorems/dd23112a-824d-4008-8915-5f1ac66e2269
-- title:
--   P2 M Global Theory is Closed Immersion equalizer   of is Separated bdcf708e7a7d: P2 M Global Theory is Closed Immersion equalizer   of is Separated bdcf708e7a7d
-- statement:
--   The P2 M Global Theory is Closed Immersion equalizer   of is Separated bdcf708e7a7d construction uses the P2 M Global Theory is Closed Immersion equalizer   of is Separated bdcf708e7a7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L39-L43

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

theorem P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d {X S T : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f) :
    IsClosedImmersion (equalizer.ι a b) := by sorry

alias «GlobalTheory».«isClosedImmersion_equalizer_ι_of_isSeparated» := P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
