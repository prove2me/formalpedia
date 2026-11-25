-- Prove2me | Theorems.Thm_PI_WGB_detPow_eq
-- name    : PI.WGB.detPow_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:49.543795+00:00
-- url     : https://prove2.me/theorems/6cb70498-152f-46f4-9170-916759409b6e
-- title:
--   WGB: det Pow eq
-- statement:
--   The WGB construction uses the det Pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L54-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem PI.WGB.detPow_eq {N : ℕ} (g : GL (Fin N) ℂ) (c : ℤ) :
    detPow ℂ N g c = ((g : Matrix (Fin N) (Fin N) ℂ).det) ^ c := by sorry
