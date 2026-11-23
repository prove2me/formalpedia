-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_l_Cl
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_l_Cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:55.363985+00:00
-- url     : https://prove2.me/theorems/9f96de1b-69e3-41f8-b599-eebf5fd4eb29
-- title:
--   L1: norm l Cl
-- statement:
--   The L1 construction uses the norm l Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L21-L22

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

theorem ReciprocityTheory.ChartRestriction.L1.norm_l_Cl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by sorry
