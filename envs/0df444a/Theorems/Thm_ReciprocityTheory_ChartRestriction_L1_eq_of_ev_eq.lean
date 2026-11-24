-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eq_of_ev_eq
-- name    : ReciprocityTheory.ChartRestriction.L1.eq_of_ev_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:25:46.369719+00:00
-- url     : https://prove2.me/theorems/9a5be4e5-ead9-4f4a-8838-3761a7a70427
-- title:
--   L1: eq of ev eq
-- statement:
--   The L1 construction uses the eq of ev eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L291-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L291-L295

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

theorem ReciprocityTheory.ChartRestriction.L1.eq_of_ev_eq {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = ev g x) : f = g := by sorry
