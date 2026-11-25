-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cw_init
-- name    : PositivityTheory.KReal.cw_init
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:38.778152+00:00
-- url     : https://prove2.me/theorems/3529fc16-dbc7-4c98-81e2-07b21f4d29e7
-- title:
--   KReal: cw init
-- statement:
--   The KReal construction uses the cw init property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L58-L65

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

theorem PositivityTheory.KReal.cw_init {r p : ℕ} (hp : p ≤ r) (c : ℚ) :
    ∑ k : Fin r, (if (k : ℕ) < p then c else 0) = p * c := by sorry
