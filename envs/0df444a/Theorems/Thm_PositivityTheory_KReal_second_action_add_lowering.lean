-- Prove2me | Theorems.Thm_PositivityTheory_KReal_second_action_add_lowering
-- name    : PositivityTheory.KReal.second_action_add_lowering
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:32.923354+00:00
-- url     : https://prove2.me/theorems/a0758b3e-e01f-4c3f-8519-f7a000c31784
-- title:
--   KReal: second action add lowering
-- statement:
--   The KReal construction uses the second action add lowering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L374-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L374-L387

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

theorem PositivityTheory.KReal.second_action_add_lowering {c d : Ix r s} (hcd : ¬ sameBlock c d) {e : ℕ} {g : Pol p q r s}
    (hg : g ∈ homog (Ix p q × Ix r s) e) :
    fockAct2 p q r s (Eab c d) g + PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈
      homog (Ix p q × Ix r s) (e + 2) := by sorry
