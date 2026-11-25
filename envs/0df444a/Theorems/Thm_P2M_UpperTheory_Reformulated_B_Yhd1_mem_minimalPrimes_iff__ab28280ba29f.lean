-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Yhd1_mem_minimalPrimes_iff__ab28280ba29f
-- name    : P2M_UpperTheory_Reformulated_B_Yhd1_mem_minimalPrimes_iff__ab28280ba29f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:32.226919+00:00
-- url     : https://prove2.me/theorems/8d374306-6fca-4f6a-b065-17108d0da482
-- title:
--   P2 M Upper Theory Reformulated B Yhd1 mem minimal Primes iff  ab28280ba29f: P2 M Upper Theory Reformulated B Yhd1 mem minimal Primes iff  ab28280ba29f
-- statement:
--   The P2 M Upper Theory Reformulated B Yhd1 mem minimal Primes iff  ab28280ba29f construction uses the P2 M Upper Theory Reformulated B Yhd1 mem minimal Primes iff  ab28280ba29f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MemMinimalPrimesIff.lean#L3-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MemMinimalPrimesIff.lean#L3-L35

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemMinimalPrimesIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Yhd1_mem_minimalPrimes_iff__ab28280ba29f.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] {z : A},
      z ≠ (0 : A) → ∀ (W : Ideal A), W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = (1 : ℕ∞) ∧ z ∈ W := by sorry

alias «UpperTheory».«Reformulated».«B».«Yhd1».«mem_minimalPrimes_iff».«» := P2M_UpperTheory_Reformulated_B_Yhd1_mem_minimalPrimes_iff__ab28280ba29f
