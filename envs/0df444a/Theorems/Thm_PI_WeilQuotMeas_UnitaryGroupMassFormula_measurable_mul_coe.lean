-- Prove2me | Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_measurable_mul_coe
-- name    : PI.WeilQuotMeas.UnitaryGroupMassFormula.measurable_mul_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:50.640155+00:00
-- url     : https://prove2.me/theorems/7ba1552b-c236-46a7-aec7-3c6a3a2f0dc3
-- title:
--   Unitary Group Mass Formula: measurable mul coe
-- statement:
--   The Unitary Group Mass Formula construction uses the measurable mul coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/LintegralMulAvgComm.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/LintegralMulAvgComm.lean#L17-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PI PI.WeilQuotMeas PI.WeilQuotMeas.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}

theorem PI.WeilQuotMeas.UnitaryGroupMassFormula.measurable_mul_coe : Measurable (fun p : G × H => p.1 * (p.2 : G)) := by sorry
