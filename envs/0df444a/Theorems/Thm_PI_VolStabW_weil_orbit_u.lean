-- Prove2me | Theorems.Thm_PI_VolStabW_weil_orbit_u
-- name    : PI.VolStabW.weil_orbit_u
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:43.545916+00:00
-- url     : https://prove2.me/theorems/2501fdad-9497-5fad-93fa-d99be77dfeda
-- title:
--   Vol Stab W: weil orbit u
-- statement:
--   The Vol Stab W construction uses the weil orbit u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabU.lean#L185-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabU.lean#L185-L260

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
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem PI.VolStabW.weil_orbit_u (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μ : Measure G) [μ.IsHaarMeasure]
    (νX : Measure X) (hnull : νX {y | ¬ ∃ g : G, g • x0 = y} = 0)
    (hinv : ∀ (g : G) (s : Set X), MeasurableSet s → νX ((fun y => g • y) ⁻¹' s) = νX s)
    (hfin : ∀ K : Set X, IsCompact K → νX K < ⊤) (hne : νX ≠ 0)
    (hemb : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0))
    (hcont : Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0)) :
    ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧
      ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) →
        ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂νX := by sorry
