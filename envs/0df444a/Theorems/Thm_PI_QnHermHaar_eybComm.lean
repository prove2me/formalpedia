-- Prove2me | Theorems.Thm_PI_QnHermHaar_eybComm
-- name    : PI.QnHermHaar.eybComm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:19.931681+00:00
-- url     : https://prove2.me/theorems/be56f23c-eb6b-475a-a886-fec2e493b99e
-- title:
--   Qn Herm Haar: eyb Comm
-- statement:
--   The Qn Herm Haar construction uses the eyb Comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnOfEq.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnOfEq.lean#L84-L93

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

theorem PI.QnHermHaar.eybComm (H : Hyp k r z z' i μ) (a b c : Fin (mdim k r i)) :
    EA H a b * YbA H c - YbA H c * EA H a b = if b = c then YbA H a else 0 := by sorry
