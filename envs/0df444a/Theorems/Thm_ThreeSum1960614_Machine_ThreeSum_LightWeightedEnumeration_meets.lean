-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightedEnumeration_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:08:21.243649+00:00
-- url     : https://prove2.me/theorems/af222f5f-c805-4099-b9b6-04adc0bea2fb
-- title:
--   Weighted subset-layer enumeration
-- statement:
--   Let $w:\mathbb N\to\mathbb N$ be coordinate weights, $W$ ambient width, $a_p$ their retained table base, and $U$ a word envelope. A program contains the same recursive enumeration body as ordinary subset enumeration. Assume addresses fit words, the weights table fits memory and $U$ fits a word. For $L\le W$, $k\le W+1$, prefix value $u$, destination $b$, correct weights in memory $\mu$, permitted depth $d+L$, and
--
--   $$u+\operatorname{total}(w,L)\le U,\qquad b+\binom Lk\le a_p,$$
--
--   the call writes the ordered cardinality-$k$ weighted sums with prefix $u$, returns $\binom Lk$, runs within the ordinary layer-enumeration budget and preserves every cell outside that output.
--
--   This reuses output-sensitive subset enumeration to generate coordinate sums needed by reporting queries.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWeightedEnumeration.lean#L66-L200

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightWeightedEnumeration
end ThreeSum.LightWeightedEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWeightedEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetEnumeration renaming time -> time
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration renaming work_pos -> work_pos
open scoped _root_.BigOperators
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.meets {pEnum W powers U : ℕ} {weights : ℕ → ℕ}
    (hprog : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : (U : ℤ) ≤ lim.word) :
    ∀ L k pref dst : ℕ, ∀ μ : ℕ → ℤ,
      L ≤ W → k ≤ W+1 → pref+_root_.ThreeSum.LightWeightedEnumeration.total weights L ≤ U →
      dst+L.choose k ≤ powers → _root_.ThreeSum.LightWeightedEnumeration.Weights μ powers W weights →
      ∀ d, d+L ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pEnum d [L,k,pref,dst,powers] μ (_root_.ThreeSum.LightSubsetEnumeration.time L k)
        (fun r μ' => r = (L.choose k : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum.LightWeightedEnumeration.output weights L k pref) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (L.choose k)) := by sorry
