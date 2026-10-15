-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_prime_divisors_card_le_log
-- name    : ThreeSum.PrimeChain.prime_divisors_card_le_log
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:44:36.769559+00:00
-- url     : https://prove2.me/theorems/59767948-68ef-4e7f-adf8-b4809dd7f854
-- title:
--   Few large prime divisors of a nonzero integer
-- statement:
--   Let $C$ be a finite set of natural primes, let $y>1$ be a natural number, and assume $p\ge y$ for every $p\in C$. For any nonzero integer $z$,
--
--   $$
--   \bigl|\{p\in C:p\mid |z|\}\bigr|\le\lfloor\log_y |z|\rfloor.
--   $$
--
--   The absolute value is interpreted as a natural number in the divisibility test. This bounds how many candidate primes can divide one nonzero difference, providing the divisor-count input to the deterministic modular-score argument.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/PrimeChain.lean#L28-L47

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.PrimeChain.prime_divisors_card_le_log : ∀ (C : Finset.{0} Nat) (y : Nat)
  (hy : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)
  (hprime :
    ∀ (p : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) C p →
        Nat.Prime p)
  (hmin :
    ∀ (p : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) C p →
        @LE.le.{0} Nat instLENat y p)
  (z : Int) (hz : @Ne.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} Nat ({p ∈ C | @Dvd.dvd.{0} Nat Nat.instDvd p z.natAbs}))
    (Nat.log y z.natAbs) := by
  sorry
