-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_exp
-- name    : PI.UnitaryCorollaryDerivatives.DjC.pres_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:46:43.730646+00:00
-- url     : https://prove2.me/theorems/5c11d4aa-a9fa-46e1-a572-b4e2599f4c45
-- title:
--   Dj C: pres exp
-- statement:
--   The Dj C construction uses the pres exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L46-L56

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
variable {N j : ℕ}
open scoped Matrix.Norms.Operator

theorem PI.UnitaryCorollaryDerivatives.DjC.pres_exp {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) :
    Pres S (NormedSpace.exp Y) := by sorry
