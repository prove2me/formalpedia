-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_mem_bot_of_fixed
-- name    : ReciprocityTheory.ChartRestriction.G.TB.mem_bot_of_fixed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:41.223739+00:00
-- url     : https://prove2.me/theorems/5c3899a4-98c5-46ab-ac58-109628968358
-- title:
--   TB: mem bot of fixed
-- statement:
--   The TB construction uses the mem bot of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/JInjCore.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/JInjCore.lean#L15-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB

theorem ReciprocityTheory.ChartRestriction.G.TB.mem_bot_of_fixed {K F : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F] (a : F)
    (ha : ∀ g : F ≃ₐ[K] F, g a = a) : a ∈ (⊥ : IntermediateField K F) := by sorry
