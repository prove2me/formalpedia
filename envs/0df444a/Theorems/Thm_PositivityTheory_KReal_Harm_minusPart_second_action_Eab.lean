-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_minusPart_second_action_Eab
-- name    : PositivityTheory.KReal.Harm.minusPart_second_action_Eab
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:23.804205+00:00
-- url     : https://prove2.me/theorems/896d43fd-42b7-5bc2-bae2-ae14c60a3eca
-- title:
--   Harm: minus Part second action Eab
-- statement:
--   The Harm construction uses the minus Part second action Eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L130-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L130-L142

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

theorem PositivityTheory.KReal.Harm.minusPart_second_action_Eab {c d : Ix r s} (h : ¬ sameBlock c d) (g : Pol p q r s) :
    minusPart (fockAct2 p q r s (Eab c d)) g = - PI.FockOneDegW.lowOp (p := p) (q := q) c d g := by sorry
