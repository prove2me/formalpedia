-- Prove2me | Theorems.Thm_PositivityTheory_KReal_low_comm
-- name    : PositivityTheory.KReal.low_comm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:27.882809+00:00
-- url     : https://prove2.me/theorems/f25228ee-82ee-495e-81a9-121a097dcb33
-- title:
--   KReal: low comm
-- statement:
--   The KReal construction uses the low comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L406-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L406-L427

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
open Harm
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.low_comm {a b c d : Ix r s} (hab : sameBlock a b) (hcd : ¬ sameBlock c d) (g : Pol p q r s) :
    fockAct2 p q r s (Eab a b) (PI.FockOneDegW.lowOp (p := p) (q := q) c d g) -
      PI.FockOneDegW.lowOp (p := p) (q := q) c d (fockAct2 p q r s (Eab a b) g) =
    (if b = c then PI.FockOneDegW.lowOp (p := p) (q := q) a d g else 0) -
      (if d = a then PI.FockOneDegW.lowOp (p := p) (q := q) c b g else 0) := by sorry
