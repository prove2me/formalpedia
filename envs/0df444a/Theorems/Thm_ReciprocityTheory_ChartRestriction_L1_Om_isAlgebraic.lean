-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Om_isAlgebraic
-- name    : ReciprocityTheory.ChartRestriction.L1.Om_isAlgebraic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:59.775906+00:00
-- url     : https://prove2.me/theorems/49fc1303-2bbd-4064-b7c9-251719c0116f
-- title:
--   L1: Om is Algebraic
-- statement:
--   The L1 construction uses the Om is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L92-L94

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

theorem ReciprocityTheory.ChartRestriction.L1.Om_isAlgebraic (d : ℕ) (x : Om d) : IsAlgebraic ℚ (x : ℂ) := by sorry
