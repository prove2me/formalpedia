-- Prove2me | Theorems.Thm_PI_QnHermHaar_ybComm
-- name    : PI.QnHermHaar.ybComm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:30.887534+00:00
-- url     : https://prove2.me/theorems/0dc48834-6936-5bd9-9cca-bb321ea51fa0
-- title:
--   Qn Herm Haar: yb Comm
-- statement:
--   The Qn Herm Haar construction uses the yb Comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnOfEq.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnOfEq.lean#L63-L66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SmoothLevZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
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

theorem PI.QnHermHaar.ybComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YbA H a * YbA H b = YbA H b * YbA H a := by sorry
