-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_natCast_Cl_of_not_dvd
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_natCast_Cl_of_not_dvd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:20.21395+00:00
-- url     : https://prove2.me/theorems/79aa7600-ce40-4d1a-a299-f9ebe6d062df
-- title:
--   L1: norm nat Cast Cl of not dvd
-- statement:
--   The L1 construction uses the norm nat Cast Cl of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L24-L26

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

theorem ReciprocityTheory.ChartRestriction.L1.norm_natCast_Cl_of_not_dvd {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by sorry
