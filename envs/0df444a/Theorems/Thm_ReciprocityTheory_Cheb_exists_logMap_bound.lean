-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_logMap_bound
-- name    : ReciprocityTheory.Cheb.exists_logMap_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:39.684178+00:00
-- url     : https://prove2.me/theorems/7673eda0-182d-5694-ba60-e836be20def2
-- title:
--   Cheb: exists log Map bound
-- statement:
--   The Cheb construction uses the exists log Map bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Support.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Support.lean#L11-L24

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

theorem ReciprocityTheory.Cheb.exists_logMap_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : mixedSpace E, (∀ i, |ucoord x i| < 1) →
    ∀ w : {w : InfinitePlace E // w ≠ w₀}, |logMap x w| ≤ B := by sorry
