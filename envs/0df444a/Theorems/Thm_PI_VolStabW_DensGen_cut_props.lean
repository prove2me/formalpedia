-- Prove2me | Theorems.Thm_PI_VolStabW_DensGen_cut_props
-- name    : PI.VolStabW.DensGen.cut_props
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:50.39365+00:00
-- url     : https://prove2.me/theorems/7cc21929-2b4f-5cc6-9c89-c24ca5526eb0
-- title:
--   Dens Gen: cut props
-- statement:
--   The Dens Gen construction uses the cut props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensGen.lean#L173-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensGen.lean#L173-L180

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

theorem PI.VolStabW.DensGen.cut_props {f' : V → X} (hf' : Continuous f') (q : V → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (ψ : X → ℝ) (hψ : Continuous ψ) (C : Set X) (hC : IsClosed C)
    (hψC : ∀ x, ψ x ≠ 0 → x ∈ C) (hCU : ∀ v, f' v ∈ C → v ∈ U) :
    Continuous (fun v => q v * ψ (f' v)) ∧ HasCompactSupport (fun v => q v * ψ (f' v)) ∧
      tsupport (fun v => q v * ψ (f' v)) ⊆ U := by sorry
