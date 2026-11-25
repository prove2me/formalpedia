-- Prove2me | Theorems.Thm_PI_QnHermHaar_repTm
-- name    : PI.QnHermHaar.repTm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:40.510864+00:00
-- url     : https://prove2.me/theorems/32d795ad-ceaa-53cd-8e1b-dd66d7408748
-- title:
--   Qn Herm Haar: rep Tm
-- statement:
--   The Qn Herm Haar construction uses the rep Tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepresentsTransferOneOne.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepresentsTransferOneOne.lean#L16-L26

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

theorem PI.QnHermHaar.repTm (H : Hyp k r z z' i μ) (w : ℂ) (a b : Fin (mdim k r i)) :
    RepOn (hI H) (Tm (EA H) w a b) (Top (EH k r) w (posL k r i a) (posL k r i b)) := by sorry
