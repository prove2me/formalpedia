-- Prove2me | Theorems.Thm_PI_KFinSmoothW_qd_conj
-- name    : PI.KFinSmoothW.qd_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:32:33.594793+00:00
-- url     : https://prove2.me/theorems/1c3ad1e4-70ed-57eb-ad11-e0de669e1817
-- title:
--   KFin Smooth W: qd conj
-- statement:
--   The KFin Smooth W construction uses the qd conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L78-L86

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

theorem PI.KFinSmoothW.qd_conj (a m : Matrix (Fin n) (Fin n) ℂ) (h1 : a * aᴴ = 1) (h2 : aᴴ * a = 1) :
    qd (a * m * aᴴ) = qd m := by sorry
