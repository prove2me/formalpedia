-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_integrable_entry
-- name    : PI.UnitaryGroupMassFormula.CommMult.integrable_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:13.855913+00:00
-- url     : https://prove2.me/theorems/0abc7466-995b-488c-898a-0022d4451dd3
-- title:
--   Comm Mult: integrable entry
-- statement:
--   The Comm Mult construction uses the integrable entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean#L19-L22

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

theorem PI.UnitaryGroupMassFormula.CommMult.integrable_entry (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {m n : Type}
    {F : H → Matrix m n ℂ} (hF : Continuous F) (i : m) (j : n) :
    Integrable (fun h => F h i j) μ := by sorry
