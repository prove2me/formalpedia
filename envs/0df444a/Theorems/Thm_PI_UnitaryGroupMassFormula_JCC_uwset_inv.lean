-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_uwset_inv
-- name    : PI.UnitaryGroupMassFormula.JCC.uwset_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:35:32.144507+00:00
-- url     : https://prove2.me/theorems/d7f873e9-6ad4-551e-9930-bc3d6a9f20b6
-- title:
--   JCC: uwset inv
-- statement:
--   The JCC construction uses the uwset inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PRhoRw.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/PRhoRw.lean#L23-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CutDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PRhoRw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.JCC
variable {k r : ℕ}

theorem PI.UnitaryGroupMassFormula.JCC.uwset_inv {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by sorry
