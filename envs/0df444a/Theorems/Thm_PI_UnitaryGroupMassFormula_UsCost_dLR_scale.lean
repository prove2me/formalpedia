-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_dLR_scale
-- name    : PI.UnitaryGroupMassFormula.UsCost.dLR_scale
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:56.267532+00:00
-- url     : https://prove2.me/theorems/0ec25b47-cf8a-4ed8-9997-a412affa5984
-- title:
--   Us Cost: d LR scale
-- statement:
--   The Us Cost construction uses the d LR scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/EntryLeLsz.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/EntryLeLsz.lean#L103-L106

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost

theorem PI.UnitaryGroupMassFormula.UsCost.dLR_scale {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : List (B.Mat k r)) (f : B.Mat k r → E) (g : B.Mat k r) :
    B.dLR u v f g = ((((u ++ v).map lsz).prod : ℝ) : ℂ) • B.dLR (u.map sc) (v.map sc) f g := by sorry
