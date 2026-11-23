-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qj15_ep_eq_one_iff
-- name    : UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:52.727844+00:00
-- url     : https://prove2.me/theorems/83a661a4-724c-4475-967e-e97ee9a6a110
-- title:
--   Qj15: ep eq one iff
-- statement:
--   The Qj15 construction uses the ep eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EpEqOneIff.lean#L3-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EpEqOneIff.lean#L3-L10

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EpEqOneIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff :
    ∀ (t : ℝ),
    Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ)) = (1 : ℂ) ↔ ∃ (n : ℤ), t = (↑n : ℝ) := by sorry
