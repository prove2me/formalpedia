-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_CapelliMiscellany_norm_natCast_prime
-- name    : UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:47.829886+00:00
-- url     : https://prove2.me/theorems/9e68cc90-5630-419a-a5ea-4f2b18a62f2f
-- title:
--   Capelli Miscellany: norm nat Cast prime
-- statement:
--   The Capelli Miscellany construction uses the norm nat Cast prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormNatCastPrime.lean#L3-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormNatCastPrime.lean#L3-L7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], ‖(↑p : PadicAlgCl p)‖ = (↑p : ℝ)⁻¹ := by sorry
