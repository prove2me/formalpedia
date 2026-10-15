-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetAddress_rank_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rank_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:08:16.810375+00:00
-- url     : https://prove2.me/theorems/48ed4b54-3540-4915-84d7-fe637f8af3d4
-- title:
--   Execution of subset-layer ranking from retained tables
-- statement:
--   Let $W$ be an ambient width, $a_t,a_p$ Pascal/power-table bases, and $p$ a recursive rank procedure with its literal recursive body in program $P$. Suppose addresses fit words, both tables fit memory and are correct in memory $\mu$, and $2^{W+1}$ fits a word. For every $L,k,m\in\mathbb N$ with $L\le W$ and $m$ a valid width-$L$, cardinality-$k$ mask, and every depth $d$ with $d+L$ allowed, the rank call returns
--
--   $$\operatorname{layerRank}(L,k,m)$$
--
--   within its prescribed $L$-dependent budget, leaving all memory unchanged.
--
--   This gives a checked compact address component for subset-transform tables.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSubsetAddress.lean#L49-L134

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rank_meets {pRank W table powers : ℕ}
    (hprog : P[pRank]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rankBody pRank)) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (htspace : table+_root_.ThreeSum.LightPascal.tableSize W ≤ lim.space)
    (hpspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : _root_.ThreeSum.LightPascal.Table μ table W) (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers W) :
    ∀ L k m : ℕ, L ≤ W → _root_.ThreeSum.SubsetAddress.IsMask L k m →
      ∀ d, d+L ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pRank d [L,k,m,W,table,powers] μ (_root_.ThreeSum.LightSubsetAddress.rankTime L)
        (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.layerRank L k m : ℤ) ∧ μ' = μ) := by sorry
