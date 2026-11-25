-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_mul_mInt
-- name    : PI.UnitaryGroupMassFormula.CommMult.mul_mInt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:14.450077+00:00
-- url     : https://prove2.me/theorems/fd4e9ea7-e7f2-4ef5-a04a-222e45a97a89
-- title:
--   Comm Mult: mul m Int
-- statement:
--   The Comm Mult construction uses the mul m Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L24-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_IntegrableEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CommMult
open MeasureTheory Matrix
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

theorem PI.UnitaryGroupMassFormula.CommMult.mul_mInt (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {l m n : Type} [Fintype m]
    (A : Matrix l m ℂ) {F : H → Matrix m n ℂ} (hF : Continuous F) :
    A * mInt μ F = mInt μ (fun h => A * F h) := by sorry
