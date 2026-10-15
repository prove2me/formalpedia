-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOriginalTripleScan_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:59:35.686869+00:00
-- url     : https://prove2.me/theorems/53bb73b8-504e-4681-b3ee-c06783d5b0d7
-- title:
--   Execution of the original-position triple-prefix scan
-- statement:
--   Let $n>0$, $t\le n^3$, magnitude bound $U$, source base $a$, input $x:\operatorname{Fin}(n)\to\mathbb Z$, and memory $\mu$ storing $x$ at $a$ be given. Assume $|x_i|\le U$, the segment fits memory, addresses fit words, the row word budget fits and depth $d+t+2$ is allowed. Let $P$ contain the recursive scan, triple-row and division bodies. Within its specified $(n,t)$ budget it returns a Boolean with
--
--   $$r=1\iff\text{one of the first }t\text{ decoded distinct-position triples sums to zero},$$
--
--   and leaves memory unchanged.
--
--   This proves the exact finite fallback scan used outside the eventual subquadratic regime.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOriginalTripleScan.lean#L23-L71

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
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

namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow
end ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BruteTripleIndex
end ThreeSum.BruteTripleIndex
namespace ThreeSum.LightOriginalTripleScan
end ThreeSum.LightOriginalTripleScan
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
end ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan
end ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOriginalTripleScan
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BruteTripleIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BruteTripleIndex
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan.meets {pMain pRow pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleScan.body pMain pRow))
    (hrow : P[pRow]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalTripleRow.body pDivide))
    (hdivide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hn : 0 < n) (ht : t ≤ n^3)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : src+n ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOriginalTripleRow.word n U : ℤ) ≤ lim.word)
    (hd : d+t+2 ≤ lim.depth)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,t] μ (_root_.ThreeSum.LightOriginalTripleScan.time n t)
      (fun result ν => (result=0 ∨ result=1) ∧ (result=1 ↔ _root_.ThreeSum.BruteTripleIndex.Hit x hn t) ∧ ν=μ) := by sorry
