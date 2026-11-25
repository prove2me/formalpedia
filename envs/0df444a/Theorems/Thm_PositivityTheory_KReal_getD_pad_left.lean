-- Prove2me | Theorems.Thm_PositivityTheory_KReal_getD_pad_left
-- name    : PositivityTheory.KReal.getD_pad_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:00.549669+00:00
-- url     : https://prove2.me/theorems/724175e6-61f2-5d13-8113-de61376a8834
-- title:
--   KReal: get D pad left
-- statement:
--   The KReal construction uses the get D pad left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L67-L71

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

theorem PositivityTheory.KReal.getD_pad_left (p k i : ℕ) (z : ℤ) :
    (pad (List.replicate p z) k []).getD i 0 = if i < p then (z : ℚ) else 0 := by sorry
