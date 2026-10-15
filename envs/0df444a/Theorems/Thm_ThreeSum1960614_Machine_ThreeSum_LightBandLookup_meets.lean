-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandLookup_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandLookup.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:39:39.536062+00:00
-- url     : https://prove2.me/theorems/3c455190-29e1-4cb0-a4fe-8ca8bdb1e2cf
-- title:
--   Band lookup agrees with the semantic lookup result
-- statement:
--   Let stored lower and upper endpoint arrays each have length $n$, with nondecreasing lower endpoints, and let the stored power table have width $W$. For query $x$, suppose $L\le W$, $n<2^L$, all stated array and word bounds hold, and depth $d+L+1$ is allowed. The lookup body and its recursive search helper return the semantic lookup result within the prescribed time and preserve memory.
--
--   This lookup contract supplies the exact semantic band result to owner-table construction while preserving its inputs.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandLookup.lean#L152-L192

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandLookup_search_meets
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct

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

theorem ThreeSum1960614.Machine.ThreeSum.LightBandLookup.meets {pMain pSearch a b n powers W L d : ℕ} {x : ℤ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hb : b+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hreadLo : ∀ i < n, μ (a+i) = lo i)
    (hreadHi : ∀ i < n, μ (b+i) = hi i)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,n,x,powers,L] μ (_root_.ThreeSum.LightBandLookup.time L)
      (fun r μ' => r = (_root_.ThreeSum.LightBandLookup.result lo hi n x : ℤ) ∧ μ' = μ) := by sorry
