-- Prove2me | Theorems.Thm_UpperTheory_map_mul_volume_of_subgroup
-- name    : UpperTheory.map_mul_volume_of_subgroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:46.344461+00:00
-- url     : https://prove2.me/theorems/66b18f6e-c9ed-4657-84cc-6244c15d9b3c
-- title:
--   Upper Theory: map mul volume of subgroup
-- statement:
--   The Upper Theory construction uses the map mul volume of subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapMulVolumeOfSubgroup.lean#L130-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapMulVolumeOfSubgroup.lean#L130-L186

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapMulVolumeOfSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set

theorem UpperTheory.map_mul_volume_of_subgroup :
    ∀ (n : ℕ) (G : Set (Fin n → Fin n → ℂ)) (μ : MeasureTheory.Measure (Fin n → Fin n → ℂ)),
        μ Gᶜ = 0 →
        (∀ a ∈ G, ‖(Matrix.of a).det‖ = 1) →
        (∀ a ∈ G, MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)) = MeasureTheory.volume) →
        (∀ a ∈ G, MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x)) μ = μ) →
        (∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) →
        ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
          μ {g | Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) ≤ R} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2)) := by sorry
