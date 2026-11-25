-- Prove2me | Theorems.Thm_PI_AprimeInfA_lintegral_mul_right_of_mem
-- name    : PI.AprimeInfA.lintegral_mul_right_of_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:22.853812+00:00
-- url     : https://prove2.me/theorems/a0456f33-3312-507a-b443-2aa33ddd4870
-- title:
--   Aprime Inf A: lintegral mul right of mem
-- statement:
--   The Aprime Inf A construction uses the lintegral mul right of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L166-L172

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

theorem PI.AprimeInfA.lintegral_mul_right_of_mem (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (ν : Measure H) [ν.IsMulLeftInvariant] (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (k : H)
    {f : G → ℝ≥0∞} (hf : Measurable f) : ∫⁻ g, f (g * k) ∂μ = ∫⁻ g, f g ∂μ := by sorry
