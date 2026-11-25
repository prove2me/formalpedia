-- Prove2me | Theorems.Thm_PI_QnHermHaar_repQminor
-- name    : PI.QnHermHaar.repQminor
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:05:44.158972+00:00
-- url     : https://prove2.me/theorems/e7eb39e3-4483-4e92-8073-8268e577a3f2
-- title:
--   Qn Herm Haar: rep Qminor
-- statement:
--   The Qn Herm Haar construction uses the rep Qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepresentsTransferOneOne.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepresentsTransferOneOne.lean#L28-L32

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

theorem PI.QnHermHaar.repQminor (H : Hyp k r z z' i μ) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) :
    RepOn (hI H) (qminor (EA H) a b w) (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w) := by sorry
