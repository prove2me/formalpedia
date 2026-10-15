-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandLookup_search_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandLookup.search_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:38:52.735075+00:00
-- url     : https://prove2.me/theorems/b7dcb332-df8e-47b4-b5dc-dec86c3c5f1c
-- title:
--   Binary band search returns the partition boundary
-- statement:
--   A recursive search procedure reads a length-$n$ array $f$ at address $a$ and a width-$W$ power table. Suppose $f$ is partitioned for query $x$ at $K$, all declared address and word bounds hold, $L\le W$, and $k\le K<k+2^L$. If depth $d+L$ is allowed, the call on these controls returns $K$ within the declared search time and leaves memory unchanged.
--
--   This search contract supplies exact partition boundaries for physical band lookup without changing endpoint storage.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandLookup.lean#L35-L126

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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBandLookup
end ThreeSum.LightBandLookup
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBandLookup
end ThreeSum1960614.Machine.ThreeSum.LightBandLookup
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandLookup
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandLookup.search_meets {pSearch a n powers W : ℕ} {x : ℤ}
    (hprog : P[pSearch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f : ℕ → ℤ) (K : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = f i)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers W)
    (hpart : _root_.ThreeSum.BinarySearch.Partition f x n K) :
    ∀ L k : ℕ, L ≤ W → k ≤ K → K < k+2^L →
      ∀ d, d+L ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pSearch d [a,n,x,powers,L,k] μ (_root_.ThreeSum.LightBandLookup.searchTime L)
        (fun r μ' => r = (K : ℤ) ∧ μ' = μ) := by sorry
