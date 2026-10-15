-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverMatrix_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:23:54.8474+00:00
-- url     : https://prove2.me/theorems/7db5d39b-aad6-405b-add4-d084a4681216
-- title:
--   Execution of the entire histogram-trimmed local-cover matrix
-- statement:
--   Let width $L$, vertex count $n>0$, modulus $p>0$, bucket cap $B$ and candidate count $N$ be natural numbers. Suppose memory stores masks $m_i<2^L$ and their Boolean rows, while candidate coefficient maps are specified by the even and odd digits of the ordered radix-$p$ enumeration. Their masks and bits end before the candidate-map base. Assume the map, two raw arrays, left/right candidate histograms and support-matrix reservations occur in that order and end before scratch, with the exact candidate scratch/word budgets fitting. Let $\lambda,P,d$ be limits, program and depth with the literal matrix closure record, addresses fitting words and $d+L+5$ allowed. It constructs the exact coefficient, histogram and support-table contract for all candidates, meets its prescribed time and preserves cells below the map base.
--
--   This realizes the deterministic cover relation as fully constructed physical tables.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverMatrix.lean#L49-L203

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
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
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverCandidate_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverMatrix
end ThreeSum.LightLocalCoverMatrix
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalCoverMatrix
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+5 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : _root_.ThreeSum.LightLocalCoverCandidate.space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ maps) (hbits : bitPtr+n*L ≤ maps) (hmaps : maps+N*(2*L) ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+N*p ≤ hist1) (hhist1 : hist1+N*p ≤ dst) (hdst : dst+N*(p*p) ≤ work)
    (hword : (_root_.ThreeSum.LightLocalCoverCandidate.word L n p cap N : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ j < N, ∀ i < L, w0 j i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) j (2*i))
    (hw1 : ∀ j < N, ∀ i < L, w1 j i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) j (2*i+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work] μ (_root_.ThreeSum.LightLocalCoverMatrix.time L n p N)
      (fun _ μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 N ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' maps) := by sorry
