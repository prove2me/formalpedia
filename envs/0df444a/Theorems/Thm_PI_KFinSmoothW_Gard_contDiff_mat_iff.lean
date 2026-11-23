-- Prove2me | Theorems.Thm_PI_KFinSmoothW_Gard_contDiff_mat_iff
-- name    : PI.KFinSmoothW.Gard.contDiff_mat_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:21.359026+00:00
-- url     : https://prove2.me/theorems/d13ce19b-1525-457c-85aa-4fc8d4e9910f
-- title:
--   Gard: cont Diff mat iff
-- statement:
--   The Gard construction uses the cont Diff mat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/Garding.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/Garding.lean#L43-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.KFinSmoothW.Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {N : WithTop ℕ∞}

theorem PI.KFinSmoothW.Gard.contDiff_mat_iff {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiff ℝ N f ↔ ∀ i j, ContDiff ℝ N (fun x => f x i j) := by sorry
