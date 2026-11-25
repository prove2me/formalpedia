-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_hasDerivAt_exp_entry
-- name    : PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:45.111305+00:00
-- url     : https://prove2.me/theorems/39014eb7-81c6-450c-852f-52266cc3ae92
-- title:
--   Dj C: has Deriv At exp entry
-- statement:
--   The Dj C construction uses the has Deriv At exp entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L86-L91

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
variable {n : Type} [Fintype n] [DecidableEq n]
open scoped Matrix.Norms.Operator

theorem PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by sorry
