-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isAlgebraic_padic_map
-- name    : ReciprocityTheory.ChartRestriction.L1.isAlgebraic_padic_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:00.270525+00:00
-- url     : https://prove2.me/theorems/5fd5cccd-ca97-4c4a-98e6-67b84ba7ce1f
-- title:
--   L1: is Algebraic padic map
-- statement:
--   The L1 construction uses the is Algebraic padic map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocC.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocC.lean#L25-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocC
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

theorem ReciprocityTheory.ChartRestriction.L1.isAlgebraic_padic_map {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {x : ℂ}
    (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ_[l] (ι x) := by sorry
