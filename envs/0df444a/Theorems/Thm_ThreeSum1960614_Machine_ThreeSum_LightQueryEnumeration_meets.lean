-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryEnumeration_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:35:56.701975+00:00
-- url     : https://prove2.me/theorems/a12bae83-f514-4f50-9ba1-b7c5077caf9e
-- title:
--   Execution of a query-restricted subset layer
-- statement:
--   Let $Q\subseteq\operatorname{Fin}(W)$ and $t\le|Q|+1$ be a requested layer. Suppose $P$ contains the query wrapper, selected-power builder, powers, erasure and recursive enumeration bodies. Let $b,w$ be output and scratch bases in memory $\mu$. Assume addresses fit words, $w+2W+2$ fits memory, $2^{W+1}$ fits a word, $b+\binom{|Q|}{t}\le w$ and $d+W+2$ is allowed. Then the program writes precisely the ordered masks of the $t$-subsets of $Q$, returns
--
--   $$\binom{|Q|}{t},$$
--
--   establishes the selected-coordinate weight table, meets its prescribed time and preserves cells below $w$ outside the output.
--
--   This supplies the physical sparse-query leaves without scanning unrelated coordinates or subsets.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightQueryEnumeration.lean#L26-L71

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Data.List.Sublists
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryWeights_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightedEnumeration_meets
import Theorems.Thm_ThreeSum_QueryCoordinates_output_missingSets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightQueryEnumeration
end ThreeSum.LightQueryEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightQueryEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets {pMain pWeights pPowers pErase pEnum : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.body pWeights pEnum))
    (hweights : P[pWeights]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body pPowers pErase))
    (hpowers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody)
    (herase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    (henum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {W t dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdst : dst+Q.card.choose t ≤ work)
    (hd : d+W+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [W,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,dst,work] μ (_root_.ThreeSum.LightQueryEnumeration.time W Q.card t)
      (fun r μ' => r = (Q.card.choose t : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst ((_root_.ThreeSum.QueryCoordinates.missingSets Q t).map _root_.ThreeSum.SubsetAddress.subsetMask) ∧
        _root_.ThreeSum.LightWeightedEnumeration.Weights μ' work Q.card (_root_.ThreeSum.QueryCoordinates.weights Q) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst (Q.card.choose t)) := by sorry
