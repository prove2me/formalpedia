-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_common_denominator_aeval_of_fg__5db326c756f9
-- name    : P2M_GlobalTheory_T_exists_common_denominator_aeval_of_fg__5db326c756f9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:17.335737+00:00
-- url     : https://prove2.me/theorems/ed6bd379-ad57-4ab1-9580-20db03d871ce
-- title:
--   P2 M Global Theory T exists common denominator aeval of fg  5db326c756f9: P2 M Global Theory T exists common denominator aeval of fg  5db326c756f9
-- statement:
--   The P2 M Global Theory T exists common denominator aeval of fg  5db326c756f9 construction uses the P2 M Global Theory T exists common denominator aeval of fg  5db326c756f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonDenominatorAevalOfFgStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonDenominatorAevalOfFgStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFgStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_common_denominator_aeval_of_fg__5db326c756f9 : ∀ (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A), (∀ x : A, ∃ p : E[X], aeval g p = x) → ∀ S : Submodule O A, S.FG → ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by sorry

alias «GlobalTheory».«T».«exists_common_denominator_aeval_of_fg'» := P2M_GlobalTheory_T_exists_common_denominator_aeval_of_fg__5db326c756f9
