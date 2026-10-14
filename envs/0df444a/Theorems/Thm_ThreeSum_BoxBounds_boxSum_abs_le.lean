-- Prove2me | Theorems.Thm_ThreeSum_BoxBounds_boxSum_abs_le
-- name    : ThreeSum.BoxBounds.boxSum_abs_le
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:38:14.206648+00:00
-- url     : https://prove2.me/theorems/91cbaa26-01a2-4eb2-bc2a-646de3406f83
-- title:
--   Uniform magnitude bound for a sparse box sum
-- statement:
--   Let $L,c,U\in\mathbb N$, and let $F,R\subseteq\{0,\ldots,L-1\}$. Let $w$ assign an integer weight to every subset of this ground set. Assume $|F|\le c$ and $|w(S)|\le U$ whenever $|S|\le c$. The box sum ranges over subsets between the required set $F\setminus R$ and the allowed set $F$. It satisfies
--
--   $$
--   \left|\sum_{F\setminus R\subseteq S\subseteq F}w(S)\right|\le 2^L U.
--   $$
--
--   This gives an explicit integer bound for stored box values, without requiring $R\subseteq F$ or any sign restriction on the weights.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BoxBounds.lean#L9-L28

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.BoxBounds.boxSum_abs_le : ∀ {L cut U : Nat} (flags free : Finset.{0} (Fin L)) (weight : Finset.{0} (Fin L) → Int)
  (hflags : @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) flags) cut)
  (hweight :
    ∀ (S : Finset.{0} (Fin L)),
      @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (weight S))
          (@Nat.cast.{0} Int instNatCastInt U)),
  @LE.le.{0} Int Int.instLEInt
    (@abs.{0} Int instLatticeInt Int.instAddGroup
      (@ThreeSum.SparseBoxes.boxSum.{0} (Fin L) (@Fin.instLinearOrder L) flags free weight))
    (@Nat.cast.{0} Int instNatCastInt
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
        U)) := by
  sorry
