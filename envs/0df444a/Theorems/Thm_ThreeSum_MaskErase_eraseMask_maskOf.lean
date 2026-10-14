-- Prove2me | Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
-- name    : ThreeSum.MaskErase.eraseMask_maskOf
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:43:28.253904+00:00
-- url     : https://prove2.me/theorems/61ef08a4-eac5-4462-b6ac-5a44b3df6a0b
-- title:
--   Deleting a mask coordinate matches set erasure
-- statement:
--   Let $L\in\mathbb N$, let $S\subseteq\{0,\ldots,L-1\}$ be finite, and let $a\in\mathbb N$. Define $M(S)=\sum_{i\in S}2^i$. The recursive mask-erasure operation $E_L(a,m)$ scans the available positions from highest to lowest and removes position $a$ if present. Then
--
--   $$E_L(a,M(S))=M(S\setminus\{a\}).$$
--
--   The coordinate $a$ need not belong to $S$ or lie below $L$. This is the exact set-level specification of the arithmetic deletion routine.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/MaskErase.lean#L43-L74

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

theorem ThreeSum.MaskErase.eraseMask_maskOf : ∀ {L : Nat} (s : Finset.{0} Nat)
  (hs :
    @LE.le.{0} (Finset.{0} Nat)
      (@Preorder.toLE.{0} (Finset.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
      s (Finset.range L))
  (a : Nat),
  @Eq.{1} Nat (ThreeSum.MaskErase.eraseMask L a (ThreeSum.SubsetAddress.maskOf s))
    (ThreeSum.SubsetAddress.maskOf (@Finset.erase.{0} Nat instDecidableEqNat s a)) := by
  sorry
