-- Prove2me | Theorems.Thm_PositivityTheory_KReal_charSplit
-- name    : PositivityTheory.KReal.charSplit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:53.320998+00:00
-- url     : https://prove2.me/theorems/85480178-ae98-43cf-b9c5-80331877077f
-- title:
--   KReal: char Split
-- statement:
--   The KReal construction uses the char Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L26-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSplit.lean#L26-L77

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit
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
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.charSplit (c : ℂ) (c0 : ℚ) (hc : c = c0) (d : ℕ) (W : Submodule ℂ (Pol p q r s))
    (hWd : W ≤ homog (Ix p q × Ix r s) d) (hW : KSt (units (fockAct1 p q r s)) W) :
    W.map (thMkC p q r s c) ≤ (W ⊓ polChi p q r s c).map (thMkC p q r s c) := by sorry
