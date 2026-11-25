-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cw_cnt_gt
-- name    : PositivityTheory.KReal.cw_cnt_gt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:04.057407+00:00
-- url     : https://prove2.me/theorems/d46d02be-34f4-5d28-867c-dca0d6ee1bbf
-- title:
--   KReal: cw cnt gt
-- statement:
--   The KReal construction uses the cw cnt gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L22-L24

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
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

theorem PositivityTheory.KReal.cw_cnt_gt {n : ℕ} (j : Fin n) (c : ℚ) :
    ∑ i : Fin n, (if i < j then c else 0) = ((j : ℕ) : ℚ) * c := by sorry
