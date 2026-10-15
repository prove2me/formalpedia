-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPairFlags_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightPairFlags.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:17.696974+00:00
-- url     : https://prove2.me/theorems/e613d448-f300-4af1-bbd6-c4e767f8a665
-- title:
--   Execution of all local pair keys and retention flags
-- statement:
--   Let $n,p>0$, width $L$, cap $B$, a Boolean row map $s_{ij}$, residue arrays $\ell_i,r_i<p$, and histogram maps $H_L,H_R\le n$ be given. Suppose memory $\mu$ stores the $nL$ bits, two length-$n$ residue rows and two length-$p$ histograms entirely before destination $b$. Assume the $2n^2$ output cells fit memory, addresses fit words, the explicit pair-flag word envelope fits, a nested call is allowed, and the program contains its division, dot-product and trimming bodies. It writes the exact pair-key array followed by the exact disjointness-and-bucket-cap flags for all $n^2$ physical pairs, within its stated time, preserving every other cell.
--
--   This builds the literal retained-edge data for the deterministic local-cover matrix.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightPairFlags.lean#L57-L242

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBooleanDot_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightTrimTest_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPairFlags
end ThreeSum.LightPairFlags
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPairFlags
end ThreeSum1960614.Machine.ThreeSum.LightPairFlags

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightPairFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightPairFlags.meets {pMain pDivide pDot pTrim : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.body pDivide pDot pTrim))
    (hdivide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hdot : P[pDot]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.body)
    (htrim : P[pTrim]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest.body)
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ dst) (hleft : leftPtr+n ≤ dst) (hright : rightPtr+n ≤ dst)
    (hleftHist : leftHist+p ≤ dst) (hrightHist : rightHist+p ≤ dst)
    (hspace : dst+2*(n*n) ≤ lim.space) (hword : (_root_.ThreeSum.LightPairFlags.word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap] μ (_root_.ThreeSum.LightPairFlags.time L n)
      (fun _ μ' =>
        (∀ i < n*n, μ' (dst+i) = (_root_.ThreeSum.LightPairFlags.pairKey n p left right i : ℤ)) ∧
        (∀ i < n*n, μ' (dst+n*n+i) = (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (2*(n*n))) := by sorry
