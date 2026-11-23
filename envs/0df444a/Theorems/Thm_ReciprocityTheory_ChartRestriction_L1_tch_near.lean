-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_near
-- name    : ReciprocityTheory.ChartRestriction.L1.tch_near
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:41.701363+00:00
-- url     : https://prove2.me/theorems/bb4a50f9-ebf4-46c9-91a4-9c74ed286ca5
-- title:
--   L1: tch near
-- statement:
--   The L1 construction uses the tch near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L55-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormNatCastClOfNotDvd.lean#L55-L104

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

theorem ReciprocityTheory.ChartRestriction.L1.tch_near (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (f : ℕ) (hf : 0 < f) (r : ℝ) (hr : r < 1)
    (h : ‖x ^ (l ^ f) - x‖ ≤ r) : ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ r := by sorry
