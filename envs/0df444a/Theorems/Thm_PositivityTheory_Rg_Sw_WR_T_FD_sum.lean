-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_FD_sum
-- name    : PositivityTheory.Rg.Sw.WR.T.FD_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:09.260859+00:00
-- url     : https://prove2.me/theorems/a97d22cb-97e9-4dcc-a5c5-db8e5e3df967
-- title:
--   T: FD sum
-- statement:
--   The T construction uses the FD sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L55-L61

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.T.FD_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (L : List (Fin n × Fin n)) : FD L (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * FD L (F i) y := by sorry
