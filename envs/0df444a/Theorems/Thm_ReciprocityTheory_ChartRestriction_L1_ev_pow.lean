-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_pow
-- name    : ReciprocityTheory.ChartRestriction.L1.ev_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:16.385847+00:00
-- url     : https://prove2.me/theorems/d5c0af1d-65cf-4adc-81c6-83a2438fc0af
-- title:
--   L1: ev pow
-- statement:
--   The L1 construction uses the ev pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L177-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L177-L181

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

theorem ReciprocityTheory.ChartRestriction.L1.ev_pow {f : PowerSeries ℂ} (hf : Conv f) (n : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f ^ n) x = ev f x ^ n := by sorry
