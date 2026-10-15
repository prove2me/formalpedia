-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverRow_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:52:57.939983+00:00
-- url     : https://prove2.me/theorems/a4bed1dd-f775-4741-a947-1c8dad6b7fa7
-- title:
--   Constructing one Boolean local-cover matrix row
-- statement:
--   Let $n>0$ stored Boolean vertex rows of width $L$ have stored left/right keys below positive $p$, with exact endpoint histogram counts at most $n$. Suppose all inputs and the $p^2$ output precede pair-key scratch, its $2n^2$ cells fit, and the complete helper, word, and depth bounds hold. The program writes the exact support indicator of independently admissible flagged vertex pairs for each endpoint pair, changing only output and scratch within its stated time.
--
--   This row theorem constructs the exact retained support indicator used by the local-cover matrix and greedy choice.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverRow.lean#L41-L106

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Data.Finset.Range
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPairFlags_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSupportMark_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverRow
end ThreeSum.LightLocalCoverRow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalCoverRow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow.Procs P pMain)
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap keys : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ keys) (hleft : leftPtr+n ≤ keys) (hright : rightPtr+n ≤ keys)
    (hleftHist : leftHist+p ≤ keys) (hrightHist : rightHist+p ≤ keys)
    (hdst : dst+p*p ≤ keys) (hspace : keys+2*(n*n) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightPairFlags.word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap,keys] μ (_root_.ThreeSum.LightLocalCoverRow.time L n p)
      (fun _ μ' =>
        (∀ r < p*p, μ' (dst+r) =
          (_root_.ThreeSum.LightSupportMark.bit (_root_.ThreeSum.LightPairFlags.pairKey n p left right)
            (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount) r (n*n) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' keys dst (p*p)) := by sorry
