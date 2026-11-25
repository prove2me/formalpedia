-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_mInt_left
-- name    : PI.UnitaryGroupMassFormula.CommMult.mInt_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:13.559841+00:00
-- url     : https://prove2.me/theorems/fbccfa2c-c688-4923-abe4-d1fe05fcce39
-- title:
--   Comm Mult: m Int left
-- statement:
--   The Comm Mult construction uses the m Int left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L45-L49

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

theorem PI.UnitaryGroupMassFormula.CommMult.mInt_left (μ : Measure H) [μ.IsMulLeftInvariant] {m n : Type} (F : H → Matrix m n ℂ)
    (g : H) : mInt μ (fun h => F (g * h)) = mInt μ F := by sorry
