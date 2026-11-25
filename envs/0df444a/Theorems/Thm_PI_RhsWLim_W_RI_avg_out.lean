-- Prove2me | Theorems.Thm_PI_RhsWLim_W_RI_avg_out
-- name    : PI.RhsWLim.W.RI.avg_out
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:18.349701+00:00
-- url     : https://prove2.me/theorems/db65c4d3-7588-4182-9dc3-5c19c9530f8e
-- title:
--   RI: avg out
-- statement:
--   The RI construction uses the avg out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvDA.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvDA.lean#L66-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.RhsWLim.W.RI.avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by sorry
