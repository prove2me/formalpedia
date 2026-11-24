-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_sub_le_max_Cl
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_Cl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:11.618162+00:00
-- url     : https://prove2.me/theorems/745a2dc6-95bc-4663-a22a-a56e3dd49d28
-- title:
--   L1: norm sub le max Cl
-- statement:
--   The L1 construction uses the norm sub le max Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L18-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.norm_sub_le_max_Cl (a b : ℂ_[l]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by sorry
