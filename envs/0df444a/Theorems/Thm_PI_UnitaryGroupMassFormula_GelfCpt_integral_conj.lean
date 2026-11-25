-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_integral_conj
-- name    : PI.UnitaryGroupMassFormula.GelfCpt.integral_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:54.086932+00:00
-- url     : https://prove2.me/theorems/4b8fbbf4-6649-4ff3-bb11-7582375e3381
-- title:
--   Gelf Cpt: integral conj
-- statement:
--   The Gelf Cpt construction uses the integral conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean#L38-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.UnitaryGroupMassFormula.GelfCpt.integral_conj (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ) (h : G) :
    ∫ g, F (h * g * h⁻¹) ∂μ = ∫ g, F g ∂μ := by sorry
