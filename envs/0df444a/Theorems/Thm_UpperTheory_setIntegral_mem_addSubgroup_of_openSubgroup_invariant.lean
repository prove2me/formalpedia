-- Prove2me | Theorems.Thm_UpperTheory_setIntegral_mem_addSubgroup_of_openSubgroup_invariant
-- name    : UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:40:34.555647+00:00
-- url     : https://prove2.me/theorems/88d41fa6-50e5-4cbc-9365-6bd1f6ca38bb
-- title:
--   Upper Theory: set Integral mem add Subgroup of open Subgroup invariant
-- statement:
--   The Upper Theory construction uses the set Integral mem add Subgroup of open Subgroup invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/SetIntegralMemAddSubgroupOfOpenSubgroupInvariant.lean#L7-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/SetIntegralMemAddSubgroupOfOpenSubgroupInvariant.lean#L7-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_SetIntegralMemAddSubgroupOfOpenSubgroupInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (J : Subgroup G), IsOpen (J : Set G) → μ (J : Set G) = 1 → ∀ S : Set G, IsCompact S → (∀ j ∈ J, ∀ g ∈ S, j * g ∈ S) → ∀ f : G → ℂ, (∀ j ∈ J, ∀ g, f (j * g) = f g) → ∀ M : AddSubgroup ℂ, (∀ g ∈ S, f g ∈ M) → ∫ g in S, f g ∂μ ∈ M := by sorry
