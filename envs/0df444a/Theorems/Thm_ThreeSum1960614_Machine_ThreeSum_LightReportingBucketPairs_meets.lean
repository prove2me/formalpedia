-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketPairs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:35:53.521754+00:00
-- url     : https://prove2.me/theorems/1566afef-6ebb-4d69-8608-cb55611ed0e3
-- title:
--   Execution of selected physical bucket-pair counting
-- statement:
--   Let original integer arrays $\ell,r$ of lengths $N_L,N_R$ and selected index arrays $i,j$ of lengths $n_L,n_R$ be correctly stored in memory $\mu$. Assume every selected index is in range, all four segments fit memory, addresses fit words, the original values and A value $a$ fit words, every $a+\ell(u)$ fits a word and $n_Ln_R$ fits a word. Let $\lambda,P,d$ be limits, program and depth with the pair and row bodies present and a nested call allowed. It returns
--
--   $$|\{(u,v):u<n_L,\ v<n_R,\ r(j_v)=a+\ell(i_u)\}|$$
--
--   within the specified selected-product time and leaves memory unchanged.
--
--   This is the exact original-value check on independently selected residue buckets.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingBucketPairs.lean#L77-L142

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketRow_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightReportingBucketPairs
end ThreeSum.LightReportingBucketPairs
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingBucketPairs
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.meets {pMain pRow srcL srcR indicesL indicesR nL nR NL NR : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.body pRow)) (hrow : P[pRow]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.body)
    (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrcL : srcL+NL ≤ lim.space) (hsrcR : srcR+NR ≤ lim.space)
    (hindicesL : indicesL+nL ≤ lim.space) (hindicesR : indicesR+nR ≤ lim.space)
    (hindexL : ∀ i < nL, indexL i < NL) (hindexR : ∀ j < nR, indexR j < NR)
    (hreadIL : ∀ i < nL, μ (indicesL+i) = (indexL i : ℤ))
    (hreadIR : ∀ j < nR, μ (indicesR+j) = (indexR j : ℤ))
    (hreadL : ∀ i < NL, μ (srcL+i) = left i) (hreadR : ∀ j < NR, μ (srcR+j) = right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ lim.word) (hvaluesR : ∀ j < NR, |right j| ≤ lim.word)
    (ha : |a| ≤ lim.word) (htarget : ∀ i < NL, |a+left i| ≤ lim.word)
    (hcountWord : ((nL*nR : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,srcL,srcR,indicesL,indicesR,nL,nR,NL,NR] μ (_root_.ThreeSum.LightReportingBucketPairs.time nL nR)
      (fun r ν => r=(_root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL : ℤ) ∧ ν=μ) := by sorry
