-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverCandidate_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:15:30.428503+00:00
-- url     : https://prove2.me/theorems/37ba5259-82c6-43c9-9d6c-14cd5de13e4e
-- title:
--   Correct construction of one local-cover candidate
-- statement:
--   Let $n>0$ masks of width $L$ and their Boolean rows be stored, with positive modulus $p$, cap $c$, and candidate index $k$. Suppose the two desired coefficient rows equal the even and odd base-$p$ digits of $k$. Under the concrete candidate interface, ordered coefficient/raw-hash/histogram/output buffers, and stated space, word, address, and depth bounds, the routine decodes both coefficient rows, constructs both exact residue histograms, and writes all $p^2$ prescribed cover entries within its stated time, with the explicit preservation contract.
--
--   Builds a candidate cover row from arithmetic and scans rather than a cover oracle. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverCandidate.lean#L57-L200

import Aesop
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverHashHistogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverRow_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightDecode_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverCandidate
end ThreeSum.LightLocalCoverCandidate
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalCoverCandidate
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask w0 w1 : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+4 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : _root_.ThreeSum.LightLocalCoverCandidate.space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ coef) (hbits : bitPtr+n*L ≤ coef) (hcoef : coef+2*L ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+p ≤ hist1) (hhist1 : hist1+p ≤ dst) (hdst : dst+p*p ≤ work)
    (hword : (_root_.ThreeSum.LightLocalCoverCandidate.word L n p cap index : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ i < L, w0 i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) index (2*i))
    (hw1 : ∀ i < L, w1 i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) index (2*i+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,p,index,n,cap,masks,bitPtr,coef,raw0,raw1,hist0,hist1,dst,work] μ
      (_root_.ThreeSum.LightLocalCoverCandidate.time L n p index)
      (fun _ μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightDecode.Rows μ' coef L p index ∧
        (∀ r < p,
          μ' (hist0+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) r n : ℤ) ∧
          μ' (hist1+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w1 w0) r n : ℤ)) ∧
        (∀ r < p*p, μ' (dst+r) = (_root_.ThreeSum.LightLocalCoverCandidate.entry L n p cap mask bits w0 w1 r : ℤ)) ∧
        _root_.ThreeSum.LightLocalCoverCandidate.Preserved μ μ' work coef raw0 raw1 hist0 hist1 dst L n p) := by sorry
