-- Prove2me | Theorems.Thm_PI_QnHermHaar_represents_transfer_one_zero
-- name    : PI.QnHermHaar.represents_transfer_one_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:58.390053+00:00
-- url     : https://prove2.me/theorems/83eaff7b-f99b-5e53-ace1-824bd68a0c35
-- title:
--   Qn Herm Haar: represents transfer one zero
-- statement:
--   The Qn Herm Haar construction uses the represents transfer one zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepresentsTransferOneOne.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepresentsTransferOneOne.lean#L53-L65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepresentsTransferOneOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem PI.QnHermHaar.represents_transfer_one_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 0)
      (tL k r z z' i Y 1 0) := by sorry
