-- Prove2me | Theorems.Thm_PI_AprimeInfA_unfold_stab
-- name    : PI.AprimeInfA.unfold_stab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:05:23.720974+00:00
-- url     : https://prove2.me/theorems/f413d683-6f4e-5560-ad6a-00fe712ea810
-- title:
--   Aprime Inf A: unfold stab
-- statement:
--   The Aprime Inf A construction uses the unfold stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L232-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/LintegralMulRightOfMem.lean#L232-L303

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
variable {X : Type} [MulAction G X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

theorem PI.AprimeInfA.unfold_stab (x0 : X) (hc : Continuous fun g : G => g • x0) (μ : Measure G)
    [μ.IsHaarMeasure] (ν : Measure (MulAction.stabilizer G x0)) (hν : ν.IsMulLeftInvariant)
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (f : G → ℝ≥0∞) (hf : Measurable f) (s : X → G)
    (hs : ∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) :
    ∫⁻ g, f g ∂μ = (ν univ)⁻¹ *
      ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂ν ∂(μ.map (fun g => g • x0)) := by sorry
