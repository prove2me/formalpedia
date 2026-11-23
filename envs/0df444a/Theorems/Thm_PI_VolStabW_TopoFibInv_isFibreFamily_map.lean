-- Prove2me | Theorems.Thm_PI_VolStabW_TopoFibInv_isFibreFamily_map
-- name    : PI.VolStabW.TopoFibInv.isFibreFamily_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:43.473389+00:00
-- url     : https://prove2.me/theorems/906a4115-03c2-4053-8f89-d8efaa0f15f0
-- title:
--   Topo Fib Inv: is Fibre Family map
-- statement:
--   The Topo Fib Inv construction uses the is Fibre Family map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoFibInv.lean#L18-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoFibInv.lean#L18-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoFibInv
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open scoped TensorProduct
variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X]

theorem PI.VolStabW.TopoFibInv.isFibreFamily_map (e : V ≃ₜ V) {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν B fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hf : ∀ x, f (e x) = f x) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν B (fun b => (fib b).map e.toMeasurableEquiv) := by sorry
