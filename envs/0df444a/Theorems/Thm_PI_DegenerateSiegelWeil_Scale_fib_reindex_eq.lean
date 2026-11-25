-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_fib_reindex_eq
-- name    : PI.DegenerateSiegelWeil.Scale.fib_reindex_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:07:36.257621+00:00
-- url     : https://prove2.me/theorems/3cfb8edf-0e6f-49ea-938c-d48bb2a71f0e
-- title:
--   Scale: fib reindex eq
-- statement:
--   The Scale construction uses the fib reindex eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/IsFibreFamilyReindex.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/IsFibreFamilyReindex.lean#L98-L108

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_FibMeas0Holds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal NNReal
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem PI.DegenerateSiegelWeil.Scale.fib_reindex_eq (e : V ≃ₜ V) (h : X ≃ₜ X) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hUo : IsOpen U)
    (heh : ∀ v, f' (e v) = h (f' v)) (hU : e ⁻¹' U = U) {cμ cν : ℝ≥0∞} (hcμ : cμ ≠ ⊤)
    (hcν : cν ≠ ⊤) (hμ : μ.map e = cμ • μ) (hν : ν.map h.symm = cν • ν)
    (hfib : IsFibreFamily μ f ι U ν univ fib) (b : X) :
    (fib (h.symm b)).map e.toMeasurableEquiv = (cμ * cν) • fib b := by sorry
