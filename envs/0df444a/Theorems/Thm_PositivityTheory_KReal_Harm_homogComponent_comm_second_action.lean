-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_homogComponent_comm_second_action
-- name    : PositivityTheory.KReal.Harm.homogComponent_comm_second_action
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:39.435647+00:00
-- url     : https://prove2.me/theorems/5368b7d5-ccc7-4e88-9917-426f4b9b76b2
-- title:
--   Harm: homog Component comm second action
-- statement:
--   The Harm construction uses the homog Component comm second action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L122-L128

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
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
open PositivityTheory.KReal.Harm
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.Harm.homogComponent_comm_second_action {a b : Ix r s} (h : sameBlock a b) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (fockAct2 p q r s (Eab a b) P) =
      fockAct2 p q r s (Eab a b) (homogeneousComponent e P) := by sorry
