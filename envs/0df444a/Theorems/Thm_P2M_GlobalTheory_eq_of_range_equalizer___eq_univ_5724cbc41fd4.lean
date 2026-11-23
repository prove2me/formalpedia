-- Prove2me | Theorems.Thm_P2M_GlobalTheory_eq_of_range_equalizer___eq_univ_5724cbc41fd4
-- name    : P2M_GlobalTheory_eq_of_range_equalizer___eq_univ_5724cbc41fd4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:13.930567+00:00
-- url     : https://prove2.me/theorems/1a9d589c-2920-4b63-ad04-70925bc860a2
-- title:
--   P2 M Global Theory eq of range equalizer   eq univ 5724cbc41fd4: P2 M Global Theory eq of range equalizer   eq univ 5724cbc41fd4
-- statement:
--   The P2 M Global Theory eq of range equalizer   eq univ 5724cbc41fd4 construction uses the P2 M Global Theory eq of range equalizer   eq univ 5724cbc41fd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L62-L68

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

theorem P2M_GlobalTheory_eq_of_range_equalizer___eq_univ_5724cbc41fd4 {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (h : Set.range (equalizer.ι a b) = Set.univ) : a = b := by sorry

alias «GlobalTheory».«eq_of_range_equalizer_ι_eq_univ» := P2M_GlobalTheory_eq_of_range_equalizer___eq_univ_5724cbc41fd4
