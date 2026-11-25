-- Prove2me | Theorems.Thm_PI_VolStabW_measure_eq_of_cos
-- name    : PI.VolStabW.measure_eq_of_cos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:43:39.700722+00:00
-- url     : https://prove2.me/theorems/4d274e75-8932-4986-ab83-443285b24509
-- title:
--   Vol Stab W: measure eq of cos
-- statement:
--   The Vol Stab W construction uses the measure eq of cos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/MeasureEqOfCos.lean#L85-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/MeasureEqOfCos.lean#L85-L101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos
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
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

theorem PI.VolStabW.measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by sorry
