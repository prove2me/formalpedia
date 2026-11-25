-- Prove2me | Theorems.Thm_PI_VolStabW_induced_eq
-- name    : PI.VolStabW.induced_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:44:50.223124+00:00
-- url     : https://prove2.me/theorems/03c4f6d6-bbd1-44f8-b3bd-9f786c616e63
-- title:
--   Vol Stab W: induced eq
-- statement:
--   The Vol Stab W construction uses the induced eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabU.lean#L51-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabU.lean#L51-L175

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal NNReal Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.VolStabW.induced_eq (H : Subgroup G) (hcl : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] (ρ' : Measure (G ⧸ H))
    (hinv : ∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s)
    (hfin : ∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) (hne : ρ' ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ q, ∫⁻ h, f (q.out * (h : G)) ∂ν ∂ρ' := by sorry
