-- Prove2me | Theorems.Thm_PI_SwBig_PhiFormProof_bigCell_eq_w0B_mul_tM
-- name    : PI.SwBig.PhiFormProof.bigCell_eq_w0B_mul_tM
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:27:56.215821+00:00
-- url     : https://prove2.me/theorems/fb85edff-4036-50ed-a0bc-9acc9e3145f1
-- title:
--   Phi Form Proof: big Cell eq w0 B mul t M
-- statement:
--   The Phi Form Proof construction uses the big Cell eq w0 B mul t M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiBigCellForm/BigCellEqW0BMulTM.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiBigCellForm/BigCellEqW0BMulTM.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiBigCellForm_BigCellEqW0BMulTM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.PhiFormProof
open PI.SwBig
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem PI.SwBig.PhiFormProof.bigCell_eq_w0B_mul_tM (k r : ℕ) (c : Fin r → ℂ) :
    bigCell k r c 1 = w0B k r * tM k r c := by sorry
