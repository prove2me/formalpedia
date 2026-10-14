-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound
-- name    : ThreeSum.SubsetAddress.enumerationWork_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:43:41.742605+00:00
-- url     : https://prove2.me/theorems/7194ca78-7064-44ab-b5cb-f8881a12d50a
-- title:
--   Enumerating one mask layer costs linear work per output
-- statement:
--   Let $L,k\in\mathbb N$. Let $E(L,k)$ be the work recurrence for the direct enumeration of all $L$-position masks with exactly $k$ selected bits. It charges recursive invocations, emitted upper masks, and cells copied while appending lower lists. Then
--
--   $$E(L,k)\le(4L+1)\binom{L}{k}+1.$$
--
--   The statement also covers empty layers with $k>L$. It bounds direct fixed-cardinality enumeration by the number of outputs rather than by the size of the entire Boolean cube.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetAddress.lean#L234-L250

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.SubsetAddress.enumerationWork_bound : ∀ (L k : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.SubsetAddress.enumerationWork L k)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) L)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (L.choose k))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  sorry
