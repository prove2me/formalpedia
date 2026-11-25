-- Prove2me | Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_lintegral_mul_avg_comm
-- name    : PI.WeilQuotMeas.UnitaryGroupMassFormula.lintegral_mul_avg_comm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:59.442804+00:00
-- url     : https://prove2.me/theorems/a5886f68-3ca6-4dfe-aff0-2d6179abf2e6
-- title:
--   Unitary Group Mass Formula: lintegral mul avg comm
-- statement:
--   The Unitary Group Mass Formula construction uses the lintegral mul avg comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/LintegralMulAvgComm.lean#L27-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/LintegralMulAvgComm.lean#L27-L52

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

theorem PI.WeilQuotMeas.UnitaryGroupMassFormula.lintegral_mul_avg_comm (μ : Measure G) (ν : Measure H) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [ν.IsInvInvariant] {f β : G → ℝ≥0∞} (hf : Measurable f)
    (hβ : Measurable β) :
    ∫⁻ g, f g * ∫⁻ h, β (g * (h : G)) ∂ν ∂μ = ∫⁻ g, β g * ∫⁻ h, f (g * (h : G)) ∂ν ∂μ := by sorry
