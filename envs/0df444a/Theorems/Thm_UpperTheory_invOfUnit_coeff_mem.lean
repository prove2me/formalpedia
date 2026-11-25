-- Prove2me | Theorems.Thm_UpperTheory_invOfUnit_coeff_mem
-- name    : UpperTheory.invOfUnit_coeff_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:47.935281+00:00
-- url     : https://prove2.me/theorems/94781303-d988-498e-85ba-468795650085
-- title:
--   Upper Theory: inv Of Unit coeff mem
-- statement:
--   The Upper Theory construction uses the inv Of Unit coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InvOfUnitCoeffMem.lean#L3-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InvOfUnitCoeffMem.lean#L3-L17

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvOfUnitCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.invOfUnit_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by sorry
