-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_gapNum_real
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.gapNum_real
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:06.32029+00:00
-- url     : https://prove2.me/theorems/2efdb9e7-a2c5-4f20-ad0d-431181c74861
-- title:
--   Lap: gap Num real
-- statement:
--   The Lap construction uses the gap Num real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/GapNum.lean#L33-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/GapNum.lean#L33-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_GapNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

theorem ReciprocityTheory.ChartRestriction.DS.Lap.gapNum_real (Q Nn T P Q0 x : ℝ) (hQ : 1 ≤ Q) (hN : 2 ≤ Nn) (hT : Nn + 5 ≤ T)
    (hP : P ≤ Nn) (hQ00 : 0 ≤ Q0) (hQ0 : Q0 ≤ Q)
    (hx : 2 * (Nn + 2 * Q * T) ^ 3 + T + 3 < x) :
    max (2 + max (3 * Nn / 2) (1 + Nn * P * Q))
      (max (16 * Nn * Q0 + 8 * Real.sqrt (2 * Q0) + 2)
        (8 * Real.sqrt (2 * Q0) * (4 * max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) + 1))) < x := by sorry
