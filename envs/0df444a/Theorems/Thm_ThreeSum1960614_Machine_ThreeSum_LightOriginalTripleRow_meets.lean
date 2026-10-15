-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOriginalTripleRow_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:03.382459+00:00
-- url     : https://prove2.me/theorems/6cca9e16-0688-4415-94cc-4671a8544d8f
-- title:
--   Execution of one original-position triple test
-- statement:
--   Let $n>0$, $t<n^3$, $U,a\in\mathbb N$, and $x:\operatorname{Fin}(n)\to\mathbb Z$ with $|x_i|\le U$. Suppose memory $\mu$ stores $x$ at $a$, that segment fits memory, addresses fit words and the explicit triple-row word budget fits. Let a Light program contain the triple-test and small-division bodies, with a nested call allowed at depth $d$. The call returns a Boolean and
--
--   $$r=1\iff\operatorname{witness}(x,n,t),$$
--
--   where the witness is the distinct-position zero-sum condition for the triple decoded from $t$. It meets the stated row-time bound and leaves memory unchanged.
--
--   This supports the exact original-input fallback for the finite exceptional size regime.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOriginalTripleRow.lean#L32-L126

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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

namespace ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
end ThreeSum1960614.Machine.ThreeSum.LightSmallDivide


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BruteTripleIndex
end ThreeSum.BruteTripleIndex
namespace ThreeSum.LightOriginalTripleRow
end ThreeSum.LightOriginalTripleRow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
end ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow
end ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOriginalTripleRow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BruteTripleIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow.meets {pMain pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow.body pDivide)) (hdivide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hn : 0 < n) (ht : t < n^3)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : src+n ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOriginalTripleRow.word n U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,t] μ (_root_.ThreeSum.LightOriginalTripleRow.time n)
      (fun result ν => (result=0 ∨ result=1) ∧
        (result=1 ↔ _root_.ThreeSum.BruteTripleIndex.witness x hn ht) ∧ ν=μ) := by sorry
