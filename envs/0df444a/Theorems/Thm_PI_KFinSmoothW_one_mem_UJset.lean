-- Prove2me | Theorems.Thm_PI_KFinSmoothW_one_mem_UJset
-- name    : PI.KFinSmoothW.one_mem_UJset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:32:42.642858+00:00
-- url     : https://prove2.me/theorems/cc920913-f1f5-463c-af03-c153c4dd2a2d
-- title:
--   KFin Smooth W: one mem UJset
-- statement:
--   The KFin Smooth W construction uses the one mem UJset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L20-L21

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

theorem PI.KFinSmoothW.one_mem_UJset : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by sorry
