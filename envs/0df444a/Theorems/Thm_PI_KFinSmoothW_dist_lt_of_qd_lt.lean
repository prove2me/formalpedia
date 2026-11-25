-- Prove2me | Theorems.Thm_PI_KFinSmoothW_dist_lt_of_qd_lt
-- name    : PI.KFinSmoothW.dist_lt_of_qd_lt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:32:51.585364+00:00
-- url     : https://prove2.me/theorems/5ce607e7-e94d-4cb1-8007-4ac70c276d61
-- title:
--   KFin Smooth W: dist lt of qd lt
-- statement:
--   The KFin Smooth W construction uses the dist lt of qd lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L88-L103

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem PI.KFinSmoothW.dist_lt_of_qd_lt {x : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 < r) (h : qd x < r ^ 2) :
    dist x 1 < r := by sorry
