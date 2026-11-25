-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_one_add_sum_le_prod
-- name    : PositivityTheory.Rg.Sw.WR.I.one_add_sum_le_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:12.047074+00:00
-- url     : https://prove2.me/theorems/c1c52701-36ac-52b5-90ba-23e0d6d84ffb
-- title:
--   I: one add sum le prod
-- statement:
--   The I construction uses the one add sum le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/Integr.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/Integr.lean#L32-L40

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.I.one_add_sum_le_prod (s : Finset (Fin n)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by sorry
