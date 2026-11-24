-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SplitFlip_IsRightTranslationIsometric_cond__7d1c9e0e004a
-- name    : P2M_GlobalTheory_SplitFlip_IsRightTranslationIsometric_cond__7d1c9e0e004a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:30:08.83281+00:00
-- url     : https://prove2.me/theorems/792a3ff1-2e79-4210-994b-336d06b0f13a
-- title:
--   P2 M Global Theory Split Flip Is Right Translation Isometric cond  7d1c9e0e004a: P2 M Global Theory Split Flip Is Right Translation Isometric cond  7d1c9e0e004a
-- statement:
--   The P2 M Global Theory Split Flip Is Right Translation Isometric cond  7d1c9e0e004a construction uses the P2 M Global Theory Split Flip Is Right Translation Isometric cond  7d1c9e0e004a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L80-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem P2M_GlobalTheory_SplitFlip_IsRightTranslationIsometric_cond__7d1c9e0e004a {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) :
    CondLE ϖ e (α / β) := by sorry

alias «GlobalTheory».«SplitFlip».«IsRightTranslationIsometric».«condν» := P2M_GlobalTheory_SplitFlip_IsRightTranslationIsometric_cond__7d1c9e0e004a
