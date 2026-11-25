-- Prove2me | Theorems.Thm_PositivityTheory_KReal_supp2
-- name    : PositivityTheory.KReal.supp2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:19.201959+00:00
-- url     : https://prove2.me/theorems/9d8f017b-090e-5aff-9dd3-a0ad03ee96d3
-- title:
--   KReal: supp2
-- statement:
--   The KReal construction uses the supp2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L353-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSupp.lean#L353-L379

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSupp
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

theorem PositivityTheory.KReal.supp2 {p q r s : ℕ} {ν : Ix r s → ℚ} {g : Pol p q r s} (hg : IsHW (fockAct2 p q r s) ν g) :
    Supp p q ν := by sorry
