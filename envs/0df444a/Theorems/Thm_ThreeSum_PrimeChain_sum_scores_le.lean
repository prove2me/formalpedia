-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le
-- name    : ThreeSum.PrimeChain.sum_scores_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:25:52.086315+00:00
-- url     : https://prove2.me/theorems/9e6a2db9-d34b-4a71-b848-f1193d9cd002
-- title:
--   Averaging bound for weighted modular scores
-- statement:
--   Let $T$ be a finite index set, $d:T\to\mathbb Z$ an integer difference assignment, and $w:\mathbb Z\to\mathbb N$ a weight function with $w(0)=0$. For $q\in\mathbb N$, set $S(q)=\sum_{i\in T,\ q\mid |d(i)|}w(d(i))$. Let $C\subseteq\mathbb N$ be finite and $K\in\mathbb N$. Suppose each nonzero $d(i)$ is divisible in absolute value by at most $K$ members of $C$. Then
--
--   $$
--   \sum_{p\in C}S(qp)\le K S(q).
--   $$
--
--   Neither primality of the members of $C$ nor positivity of $q$ is required. Zero differences contribute no weight, so the estimate remains valid when genuine zero-sum witnesses are present.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/PrimeChain.lean#L61-L85

import Definitions.Def_ThreeSum1962Source_Bundle01
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

universe u_1

theorem ThreeSum.PrimeChain.sum_scores_le : ∀ {ι : Type u_1} (T : Finset.{u_1} ι) (difference : ι → Int) (weight : Int → Nat)
  (hzero :
    @Eq.{1} Nat (weight (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (C : Finset.{0} Nat) (q K : Nat)
  (hdivisors :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) T i →
        @Ne.{1} Int (difference i) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @LE.le.{0} Nat instLENat
            (@Finset.card.{0} Nat ({p ∈ C | @Dvd.dvd.{0} Nat Nat.instDvd p (difference i).natAbs})) K),
  @LE.le.{0} Nat instLENat
    (∑ p ∈ C,
      @ThreeSum.PrimeChain.score.{u_1} ι T difference weight
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q p))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K
      (@ThreeSum.PrimeChain.score.{u_1} ι T difference weight q)) := by
  sorry
