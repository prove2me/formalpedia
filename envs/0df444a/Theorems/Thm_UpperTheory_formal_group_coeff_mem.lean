-- Prove2me | Theorems.Thm_UpperTheory_formal_group_coeff_mem
-- name    : UpperTheory.formal_group_coeff_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:52.622575+00:00
-- url     : https://prove2.me/theorems/e50b26fc-8554-4caa-b302-5eb925a7fd0a
-- title:
--   Upper Theory: formal group coeff mem
-- statement:
--   The Upper Theory construction uses the formal group coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FormalGroupCoeffMem.lean#L30-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FormalGroupCoeffMem.lean#L30-L68

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FormalGroupCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.formal_group_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (a₁ a₂ a₃ a₄ a₆ : R) (w : PowerSeries R), a₁ ∈ S → a₂ ∈ S → a₃ ∈ S → a₄ ∈ S → a₆ ∈ S → PowerSeries.constantCoeff w = 0 → w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * PowerSeries.X * w + PowerSeries.C a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C a₃ * w ^ 2 + PowerSeries.C a₄ * PowerSeries.X * w ^ 2 + PowerSeries.C a₆ * w ^ 3 → ∀ n, PowerSeries.coeff n w ∈ S := by sorry
