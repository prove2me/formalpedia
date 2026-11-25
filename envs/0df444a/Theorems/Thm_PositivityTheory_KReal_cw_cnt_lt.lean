-- Prove2me | Theorems.Thm_PositivityTheory_KReal_cw_cnt_lt
-- name    : PositivityTheory.KReal.cw_cnt_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:03.786013+00:00
-- url     : https://prove2.me/theorems/bdd3884f-b361-5439-a1b0-8d17a3fb8f69
-- title:
--   KReal: cw cnt lt
-- statement:
--   The KReal construction uses the cw cnt lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasW.lean#L14-L20

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

theorem PositivityTheory.KReal.cw_cnt_lt {n : ℕ} (i : Fin n) (c : ℚ) :
    ∑ j : Fin n, (if i < j then c else 0) = ((n : ℚ) - 1 - (i : ℕ)) * c := by sorry
