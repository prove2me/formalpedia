-- Prove2me | Theorems.Thm_PI_QnHermHaar_starE_A
-- name    : PI.QnHermHaar.starE_A
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:00:41.956907+00:00
-- url     : https://prove2.me/theorems/e54bfab8-c99d-48a7-8c9d-964314acd8c3
-- title:
--   Qn Herm Haar: star E A
-- statement:
--   The Qn Herm Haar construction uses the star E A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnOfEq.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnOfEq.lean#L46-L56

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

theorem PI.QnHermHaar.starE_A (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    star (EA H a b) = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d := by sorry
