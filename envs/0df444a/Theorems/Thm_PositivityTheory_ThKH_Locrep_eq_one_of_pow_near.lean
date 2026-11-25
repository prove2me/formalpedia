-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_eq_one_of_pow_near
-- name    : PositivityTheory.ThKH.Locrep.eq_one_of_pow_near
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:59.806888+00:00
-- url     : https://prove2.me/theorems/3864e563-1881-4c35-8cc8-9feb68655a57
-- title:
--   Locrep: eq one of pow near
-- statement:
--   The Locrep construction uses the eq one of pow near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideBis
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LinearIndependentOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology

theorem PositivityTheory.ThKH.Locrep.eq_one_of_pow_near {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R} (h : ∀ p : ℕ, ‖a ^ p - 1‖ < 1 / 2) :
    a = 1 := by sorry
