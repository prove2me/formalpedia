-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_minus1_eq
-- name    : PositivityTheory.KReal.Harm.minus1_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:11.889409+00:00
-- url     : https://prove2.me/theorems/3b81088f-75ee-5b5b-9729-e0a6fc03eddf
-- title:
--   Harm: minus1 eq
-- statement:
--   The Harm construction uses the minus1 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L166-L171

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
open PI.FockOneDegW.Swap

theorem PositivityTheory.KReal.Harm.minus1_eq (Z : Mat p q) (hZ : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s Z) P = -∑ a, ∑ b, Z a b • low1 a b P := by sorry
