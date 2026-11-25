-- Prove2me | Theorems.Thm_PI_QnHermHaar_sum_four_comm_version
-- name    : PI.QnHermHaar.sum_four_comm_version
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:13.277151+00:00
-- url     : https://prove2.me/theorems/e03ef8d4-ee42-4ebb-a7a9-3cd6e96e5755
-- title:
--   Qn Herm Haar: sum four comm version
-- statement:
--   The Qn Herm Haar construction uses the sum four comm version property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L112-L118

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnHermHaar.sum_four_comm_version {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → A) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by sorry
