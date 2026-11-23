-- Prove2me | Theorems.Thm_PI_AprimeInfA_avg_out
-- name    : PI.AprimeInfA.avg_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:21.597278+00:00
-- url     : https://prove2.me/theorems/06369fff-2c84-47e3-89b9-3cedb40720a7
-- title:
--   Aprime Inf A: avg out
-- statement:
--   The Aprime Inf A construction uses the avg out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L190-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L190-L195

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfA
open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.AprimeInfA.avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by sorry
