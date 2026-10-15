-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRowScan_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:17:22.06329+00:00
-- url     : https://prove2.me/theorems/e395b6e8-5dce-4212-9bc2-1fc303fb3c66
-- title:
--   Execution of endpoint cardinality and paired one-hot hashes
-- statement:
--   Let $L,U\in\mathbb N$, bit map $s$ and nonnegative weight maps $w_0,w_1$ be given, with $s_i\le1$ and both weights at most $U$ for $i<L$. Suppose their three length-$L$ arrays are stored in memory $\mu$, all those arrays and a three-cell destination $b$ fit memory, addresses fit words and the explicit row-scan word budget fits. For limits, program and depth $\lambda,P,d$ with the scan body present, the procedure writes the cardinality $\sum_{i<L}s_i$ and the two complementary one-hot hash sums at $b,b+1,b+2$. It meets its specified linear scan time and changes no other cell.
--
--   This computes the literal endpoint statistics used for independent trimming and modular source encoding.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceRowScan.lean#L83-L180

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceRowScan
end ThreeSum.LightSourceRowScan
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceRowScan
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.meets {pMain : ℕ} (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.body)
    {μ : ℕ → ℤ} {src src0 src1 L dst U : ℕ} (bits w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+L ≤ lim.space) (hsrc0 : src0+L ≤ lim.space)
    (hsrc1 : src1+L ≤ lim.space) (hdst : dst+3 ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceRowScan.word L U : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,src0,src1,L,dst] μ (_root_.ThreeSum.LightSourceRowScan.time L) (fun _ ν =>
      ν dst = (_root_.ThreeSum.LightSourceRowScan.count bits L : ℤ) ∧
      ν (dst+1) = (_root_.ThreeSum.LightSourceRowScan.hash bits w0 w1 L : ℤ) ∧
      ν (dst+2) = (_root_.ThreeSum.LightSourceRowScan.hash bits w1 w0 L : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst 3) := by sorry
