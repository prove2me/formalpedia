-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
-- name    : ThreeSum.SourceBuckets.position_bucket_iff
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:25:53.57224+00:00
-- url     : https://prove2.me/theorems/aa91bf09-d720-4100-95c9-e49c4014645d
-- title:
--   Bucket intervals characterize the stored key
-- statement:
--   Let $k:\mathbb N\to\mathbb N$ and $N\in\mathbb N$. Put $C_r(t)=|\{a<t:k(a)=r\}|$, $O_r=\sum_{s<r}C_s(N)$, and $P(i)=O_{k(i)}+C_{k(i)}(i)$. For every $i<N$ and $r\in\mathbb N$,
--
--   $$
--   O_r\le P(i)<O_{r+1}\quad\Longleftrightarrow\quad k(i)=r.
--   $$
--
--   The equivalence identifies exactly which original indices occupy each contiguous bucket segment. It is valid without a global bound on the key values.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBuckets.lean#L95-L108

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram

theorem ThreeSum.SourceBuckets.position_bucket_iff : ∀ {key : Nat → Nat} {N i r : Nat} (hi : @LT.lt.{0} Nat instLTNat i N),
  Iff
    (And (@LE.le.{0} Nat instLENat (ThreeSum.SourceBuckets.offset key N r) (ThreeSum.SourceBuckets.position key N i))
      (@LT.lt.{0} Nat instLTNat (ThreeSum.SourceBuckets.position key N i)
        (ThreeSum.SourceBuckets.offset key N
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@Eq.{1} Nat (key i) r) := by
  sorry
