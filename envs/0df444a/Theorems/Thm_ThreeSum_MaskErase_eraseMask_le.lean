-- Prove2me | Theorems.Thm_ThreeSum_MaskErase_eraseMask_le
-- name    : ThreeSum.MaskErase.eraseMask_le
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:44:31.383096+00:00
-- url     : https://prove2.me/theorems/e06adacc-e37e-45f3-bbea-e2ce69ebb9a4
-- title:
--   Erasing a mask coordinate never increases its value
-- statement:
--   Let $L,a,m\in\mathbb N$ with $m<2^L$. The recursive operation $\operatorname{eraseMask}(L,a,m)$ inspects the binary positions below $L$ and removes position $a$ if present. Then
--
--   $$
--   \operatorname{eraseMask}(L,a,m)\le m.
--   $$
--
--   The coordinate $a$ need not lie below $L$. This gives a numerical bound on the mask-erasure result that can be used in subsequent word-size and address checks.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/MaskErase.lean#L23-L34

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
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.MaskErase.eraseMask_le : ∀ {L a m : Nat}
  (hm :
    @LT.lt.{0} Nat instLTNat m
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)),
  @LE.le.{0} Nat instLENat (ThreeSum.MaskErase.eraseMask L a m) m := by
  sorry
