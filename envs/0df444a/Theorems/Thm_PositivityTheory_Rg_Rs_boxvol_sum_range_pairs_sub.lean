-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_boxvol_sum_range_pairs_sub
-- name    : PositivityTheory.Rg.Rs.boxvol.sum_range_pairs_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:28.813954+00:00
-- url     : https://prove2.me/theorems/ca2068ba-ff4a-5917-a57f-d50753d5064e
-- title:
--   boxvol: sum range pairs sub
-- statement:
--   The boxvol construction uses the sum range pairs sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/BoxVolumes/SumRangeSuccMulSubPred.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/BoxVolumes/SumRangeSuccMulSubPred.lean#L17-L32

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_BoxVolumes_SumRangeSuccMulSubPred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.boxvol

theorem PositivityTheory.Rg.Rs.boxvol.sum_range_pairs_sub (y : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, ∑ i ∈ range j, (y i - y j)
      = ∑ r ∈ range n, ((r : ℝ) * ((n : ℝ) - r)) * (y (r - 1) - y r) := by sorry
