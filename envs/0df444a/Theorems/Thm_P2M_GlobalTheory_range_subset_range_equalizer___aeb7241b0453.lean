-- Prove2me | Theorems.Thm_P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453
-- name    : P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:47.973893+00:00
-- url     : https://prove2.me/theorems/266d258d-40df-4cbf-86e0-7d3e61fe309e
-- title:
--   P2 M Global Theory range subset range equalizer   aeb7241b0453: P2 M Global Theory range subset range equalizer   aeb7241b0453
-- statement:
--   The P2 M Global Theory range subset range equalizer   aeb7241b0453 construction uses the P2 M Global Theory range subset range equalizer   aeb7241b0453 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L57-L60

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

theorem P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453 {X T Z : Scheme.{u}} {a b : T ⟶ X} (j : Z ⟶ T)
    (hj : j ≫ a = j ≫ b) : Set.range j ⊆ Set.range (equalizer.ι a b) := by sorry

alias «GlobalTheory».«range_subset_range_equalizer_ι» := P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453
