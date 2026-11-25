-- Prove2me | Theorems.Thm_UpperTheory_prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow
-- name    : UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:18.957934+00:00
-- url     : https://prove2.me/theorems/49768b95-ca8a-43a8-83c1-69e9a4041f79
-- title:
--   Upper Theory: prod prime Factors pow ceil padic Val Nat mul eq pow
-- statement:
--   The Upper Theory construction uses the prod prime Factors pow ceil padic Val Nat mul eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/ProdPrimeFactorsPowCeilPadicValNatMulEqPow.lean#L3-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/ProdPrimeFactorsPowCeilPadicValNatMulEqPow.lean#L3-L20

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ProdPrimeFactorsPowCeilPadicValNatMulEqPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow :
    ∀ (Q T a b : ℕ), Q ≠ 0 → ∏ p ∈ Q.primeFactors.filter Nat.Prime,
      p ^ (T * ⌈(padicValNat p Q : ℝ) * (a : ℝ)⌉.toNat + ⌈(padicValNat p Q : ℝ) * (b : ℝ)⌉.toNat) = Q ^ (T * a + b) := by sorry
