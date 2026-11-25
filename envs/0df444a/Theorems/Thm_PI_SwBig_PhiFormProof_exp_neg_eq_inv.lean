-- Prove2me | Theorems.Thm_PI_SwBig_PhiFormProof_exp_neg_eq_inv
-- name    : PI.SwBig.PhiFormProof.exp_neg_eq_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:27:44.972419+00:00
-- url     : https://prove2.me/theorems/3ee0ec91-ada1-5757-b9aa-31a546b1c4a2
-- title:
--   Phi Form Proof: exp neg eq inv
-- statement:
--   The Phi Form Proof construction uses the exp neg eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiBigCellForm/BigCellEqW0BMulTM.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PhiBigCellForm/BigCellEqW0BMulTM.lean#L21-L23

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

theorem PI.SwBig.PhiFormProof.exp_neg_eq_inv (k r : ℕ) (X : Mat k r) :
    NormedSpace.exp (-X) = (NormedSpace.exp X)⁻¹ := by sorry
