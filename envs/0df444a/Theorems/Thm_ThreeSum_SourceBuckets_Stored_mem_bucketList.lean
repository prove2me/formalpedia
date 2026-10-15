-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_Stored_mem_bucketList
-- name    : ThreeSum.SourceBuckets.Stored.mem_bucketList
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:54:18.550475+00:00
-- url     : https://prove2.me/theorems/11031b84-83c4-4334-9f1c-5f05ca3f4756
-- title:
--   A stored bucket contains exactly the source indices with its key
-- statement:
--   Let $N,M,o,f,r,i$ be natural numbers, let $\kappa:\mathbb N\to\mathbb N$ satisfy $\kappa(j)<M$ for $j<N$, and let $\mu$ store the stable bucket representation of these $N$ indices at offset base $o$ and flat-array base $f$. For a valid key $r<M$, define
--   $$D_r=\#\{j<N:\kappa(j)=r\},\qquad O_r=\sum_{s<r}D_s.$$
--   Let $L_r$ be the list read from the $D_r$ consecutive memory cells starting at $f+O_r$, interpreting their stored integers as natural indices. Then
--   $$i\in L_r\quad\Longleftrightarrow\quad i<N\ \land\ \kappa(i)=r.$$
--
--   This identifies physical bucket contents with their exact source-index semantics, including distinct indices whose input values coincide.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBuckets.lean#L152-L168

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram

theorem ThreeSum.SourceBuckets.Stored.mem_bucketList : ∀ {μ : Nat → Int} {key : Nat → Nat} {N M offsets flat r i : Nat}
  (H : ThreeSum.SourceBuckets.Stored μ key N M offsets flat)
  (hkey : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i N → @LT.lt.{0} Nat instLTNat (key i) M)
  (hr : @LT.lt.{0} Nat instLTNat r M),
  Iff
    (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (ThreeSum.SourceBuckets.bucketList μ flat (ThreeSum.SourceBuckets.offset key N r)
        (ThreeSum.LightHistogram.count key r N))
      i)
    (And (@LT.lt.{0} Nat instLTNat i N) (@Eq.{1} Nat (key i) r)) := by
  sorry
