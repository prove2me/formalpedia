-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_mInt_mul
-- name    : PI.UnitaryGroupMassFormula.CommMult.mInt_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:14.284805+00:00
-- url     : https://prove2.me/theorems/5ac1e25f-04d5-413a-b63a-b32b54c09065
-- title:
--   Comm Mult: m Int mul
-- statement:
--   The Comm Mult construction uses the m Int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L32-L38

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

theorem PI.UnitaryGroupMassFormula.CommMult.mInt_mul (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {l m n : Type} [Fintype m]
    {F : H → Matrix l m ℂ} (hF : Continuous F) (B : Matrix m n ℂ) :
    mInt μ F * B = mInt μ (fun h => F h * B) := by sorry
