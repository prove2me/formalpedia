-- Prove2me | Theorems.Thm_ThreeSum_SourceBuckets_position_injective
-- name    : ThreeSum.SourceBuckets.position_injective
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:25:51.735981+00:00
-- url     : https://prove2.me/theorems/eec4ea7d-386b-40df-8ff6-5b0b5561c79c
-- title:
--   Counting-sort positions preserve distinct indices
-- statement:
--   Let $k:\mathbb N\to\mathbb N$ be a key function and $N\in\mathbb N$. Define $C_r(t)=|\{a<t:k(a)=r\}|$, $O_r=\sum_{s<r}C_s(N)$, and the counting-sort position $P(i)=O_{k(i)}+C_{k(i)}(i)$. For indices $i,j<N$,
--
--   $$
--   P(i)=P(j)\quad\Longrightarrow\quad i=j.
--   $$
--
--   No upper bound on the key values is required. Thus the retained bucket layout keeps distinct physical input indices separate even when their keys coincide.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SourceBuckets.lean#L76-L93

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

theorem ThreeSum.SourceBuckets.position_injective : ∀ {key : Nat → Nat} {N i j : Nat} (hi : @LT.lt.{0} Nat instLTNat i N) (hj : @LT.lt.{0} Nat instLTNat j N)
  (he : @Eq.{1} Nat (ThreeSum.SourceBuckets.position key N i) (ThreeSum.SourceBuckets.position key N j)),
  @Eq.{1} Nat i j := by
  sorry
