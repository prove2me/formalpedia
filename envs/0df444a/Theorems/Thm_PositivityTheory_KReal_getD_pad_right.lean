-- Prove2me | Theorems.Thm_PositivityTheory_KReal_getD_pad_right
-- name    : PositivityTheory.KReal.getD_pad_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:16.873596+00:00
-- url     : https://prove2.me/theorems/da598659-e967-5b78-a53d-860356bdb338
-- title:
--   KReal: get D pad right
-- statement:
--   The KReal construction uses the get D pad right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L73-L77

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal

theorem PositivityTheory.KReal.getD_pad_right (q r i : ℕ) (z : ℤ) (hq : q ≤ r) (hi : i < r) :
    (pad [] (r - q) (List.replicate q z)).getD i 0 = if r ≤ i + q then (z : ℚ) else 0 := by sorry
