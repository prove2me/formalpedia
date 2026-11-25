-- Prove2me | Theorems.Thm_PositivityTheory_KReal_nontrivial_of_pair
-- name    : PositivityTheory.KReal.nontrivial_of_pair
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:55.037203+00:00
-- url     : https://prove2.me/theorems/e1f769b7-9fec-51ec-9891-8913e62b7b04
-- title:
--   KReal: nontrivial of pair
-- statement:
--   The KReal construction uses the nontrivial of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreNonv.lean#L160-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreNonv.lean#L160-L238

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
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

theorem PositivityTheory.KReal.nontrivial_of_pair {p q r s : ℕ} (c : ℂ) (c0 : ℚ) (hc : c = c0) (h : PairData p q r s c) :
    Nontrivial (ThC p q r s c) := by sorry
