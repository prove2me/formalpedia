-- Prove2me | Theorems.Thm_PI_VolStabW_LocPosW_pos_of_lb
-- name    : PI.VolStabW.LocPosW.pos_of_lb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:13.018555+00:00
-- url     : https://prove2.me/theorems/9bc46321-39e2-4d6f-82fc-f2ec1b7a1fe6
-- title:
--   Loc Pos W: pos of lb
-- statement:
--   The Loc Pos W construction uses the pos of lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensPos.lean#L16-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensPos.lean#L16-L126

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FreeOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensPos
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
  Filter Topology Set
open scoped TensorProduct ENNReal
open PI.VolStabW.LocPosW

theorem PI.VolStabW.LocPosW.pos_of_lb {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} (hι : Function.Injective ι)
    {U : Set V} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    {f' : V → X} (hf' : Continuous f') (hff : ∀ v, f v = ι (f' v))
    {φ : V → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ v, 0 ≤ φ v) {W : Set V} (hWU : W ⊆ U) {δ : ℝ} (hδ : 0 < δ)
    (hWφ : ∀ v ∈ W, δ ≤ φ v) {b0 : X} {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ⊤) {N : Set X}
    (hN : N ∈ 𝓝 b0) (hlb : ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W))
    (hνpos : ∀ O : Set X, IsOpen O → O.Nonempty → ν O ≠ 0) (hνfin : ∃ N' ∈ 𝓝 b0, ν N' < ⊤) :
    0 < ∫ v, φ v ∂(fib b0) := by sorry
