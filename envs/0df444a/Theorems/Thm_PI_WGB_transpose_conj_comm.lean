-- Prove2me | Theorems.Thm_PI_WGB_transpose_conj_comm
-- name    : PI.WGB.transpose_conj_comm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:16.786629+00:00
-- url     : https://prove2.me/theorems/ec606d27-88aa-4583-82b5-9a77ced4ce67
-- title:
--   WGB: transpose conj comm
-- statement:
--   The WGB construction uses the transpose conj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L10-L12

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

theorem PI.WGB.transpose_conj_comm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    M.transpose.conjTranspose = M.conjTranspose.transpose := by sorry
