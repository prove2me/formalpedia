-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_support_bound
-- name    : ReciprocityTheory.Cheb.exists_support_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:49.253793+00:00
-- url     : https://prove2.me/theorems/83e46d90-6dff-4d22-9329-e4dd799a38f6
-- title:
--   Cheb: exists support bound
-- statement:
--   The Cheb construction uses the exists support bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Support.lean#L81-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Support.lean#L81-L106

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_Support
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.exists_support_bound : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ ∀ x : mixedSpace E, uphi x ≠ 0 →
    (∀ w : InfinitePlace E, c₀ * ‖x‖ ≤ normAtPlace w x) ∧
      c₀ ^ Module.finrank ℚ E * ‖x‖ ^ Module.finrank ℚ E ≤ mixedEmbedding.norm x := by sorry
