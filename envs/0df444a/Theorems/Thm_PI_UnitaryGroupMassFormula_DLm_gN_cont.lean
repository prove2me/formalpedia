-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_gN_cont
-- name    : PI.UnitaryGroupMassFormula.DLm.gN_cont
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:44:15.080307+00:00
-- url     : https://prove2.me/theorems/f02670e6-dc54-57a6-948f-526acdeb686c
-- title:
--   DLm: g N cont
-- statement:
--   The DLm construction uses the g N cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PointwiseBoundHolds.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PointwiseBoundHolds.lean#L17-L19

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFibreBoundDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PointwiseBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm

theorem PI.UnitaryGroupMassFormula.DLm.gN_cont (k r : ℕ) : Continuous (fun g : B.Mat k r => B.gN g) := by sorry
