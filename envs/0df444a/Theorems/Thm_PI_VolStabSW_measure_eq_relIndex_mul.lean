-- Prove2me | Theorems.Thm_PI_VolStabSW_measure_eq_relIndex_mul
-- name    : PI.VolStabSW.measure_eq_relIndex_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:35.073448+00:00
-- url     : https://prove2.me/theorems/fa75a198-058b-45d5-9d9b-f9c80015a51e
-- title:
--   Vol Stab SW: measure eq rel Index mul
-- statement:
--   The Vol Stab SW construction uses the measure eq rel Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHI.lean#L11-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHI.lean#L11-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

theorem PI.VolStabSW.measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (Λ L : AddSubgroup V) (hΛL : Λ ≤ L)
    (hL : MeasurableSet (L : Set V)) (hΛ : MeasurableSet (Λ : Set V)) (hfin : Λ.relIndex L ≠ 0) :
    μ L = (Λ.relIndex L : ENNReal) * μ Λ := by sorry
