-- Prove2me | Theorems.Thm_UpperTheory_map_left_mul_volume_eq
-- name    : UpperTheory.map_left_mul_volume_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:52.611537+00:00
-- url     : https://prove2.me/theorems/3e3edd73-6aa7-4711-8234-80029e0b90a5
-- title:
--   Upper Theory: map left mul volume eq
-- statement:
--   The Upper Theory construction uses the map left mul volume eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapLeftMulVolumeEq.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapLeftMulVolumeEq.lean#L23-L42

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapLeftMulVolumeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.map_left_mul_volume_eq :
    ∀ (n : ℕ) (a : Fin n → Fin n → ℂ), ‖(Matrix.of a).det‖ = 1 →
        MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)) = MeasureTheory.volume := by sorry
