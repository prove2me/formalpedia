-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cw_blk
-- name    : PositivityTheory.KReal.cw_blk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:29.617402+00:00
-- url     : https://prove2.me/theorems/6ea80969-0455-4849-8caf-5840a21ab07a
-- title:
--   KReal: cw blk
-- statement:
--   The KReal construction uses the cw blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L26-L35

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

theorem PositivityTheory.KReal.cw_blk {n : ℕ} (f : Fin n → ℚ) :
    ∑ i, ∑ j, (if i < j then f i - f j else 0) = ∑ i : Fin n, ((n : ℚ) - 1 - 2 * (i : ℕ)) * f i := by sorry
