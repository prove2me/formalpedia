-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_Aio
-- name    : ReciprocityTheory.ChartRestriction.L1.mem_Aio
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:57:07.694469+00:00
-- url     : https://prove2.me/theorems/0e1e7681-641e-401d-8913-94ad75ff193e
-- title:
--   L1: mem Aio
-- statement:
--   The L1 construction uses the mem Aio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L10-L13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.mem_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) : x ∈ Aio d l ι ↔ ‖ι (x : ℂ)‖ ≤ 1 := by sorry
