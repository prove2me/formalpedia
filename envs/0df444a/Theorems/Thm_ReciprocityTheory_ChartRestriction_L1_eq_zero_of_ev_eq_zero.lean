-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eq_zero_of_ev_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.eq_zero_of_ev_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:38.613332+00:00
-- url     : https://prove2.me/theorems/f3c0b382-3b89-4812-b436-693e70bdff01
-- title:
--   L1: eq zero of ev eq zero
-- statement:
--   The L1 construction uses the eq zero of ev eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L284-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L284-L289

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.eq_zero_of_ev_eq_zero {f : PowerSeries ℂ} (hf : Conv f)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = 0) : f = 0 := by sorry
