-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_natCast_Cl
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_natCast_Cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:44.941476+00:00
-- url     : https://prove2.me/theorems/abb974b4-9c6a-48e4-a981-82869bd0d3d1
-- title:
--   L1: norm nat Cast Cl
-- statement:
--   The L1 construction uses the norm nat Cast Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L13-L16

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

theorem ReciprocityTheory.ChartRestriction.L1.norm_natCast_Cl (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by sorry
