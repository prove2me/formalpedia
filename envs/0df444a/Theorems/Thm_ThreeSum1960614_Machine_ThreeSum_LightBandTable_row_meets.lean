-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandTable_row_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandTable.row_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:53:20.339926+00:00
-- url     : https://prove2.me/theorems/44a2eee1-18e4-4a3c-bf43-d83a32122c5e
-- title:
--   Constructing a band-lookup table row
-- statement:
--   Let stored values $f$ of length $n$, endpoint arrays $\mathrm{lo},\mathrm{hi}$ of length $m$, and a width-$W$ power table satisfy the stated ordered-disjoint layout and memory bounds. Assume nondecreasing lower endpoints, $m<2^W$, query $|x|\le U$, source values bounded by $U$, sign $|s|\le1$, required word bounds, and depth $d+W+2$. The installed row, lookup, and search procedures write each semantic row value at the destination, within the row-time bound, changing only that row.
--
--   This row contract computes the owner lookup values needed to construct the complete band-enumeration tables.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandTable.lean#L31-L105

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandLookup_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBandTable
end ThreeSum.LightBandTable
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBandTable
end ThreeSum1960614.Machine.ThreeSum.LightBandTable
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandTable
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandTable.row_meets {pRow pLookup pSearch b loBase hiBase n m dst powers W d U : ℕ}
    {x s : ℤ} (hrow : P[pRow]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.rowBody pLookup))
    (hlookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hb : b+n ≤ dst) (hlo : loBase+m ≤ dst) (hhi : hiBase+m ≤ dst)
    (hdst : dst+n ≤ powers) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hqueryWord : 2*(U : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (b+j) = f j)
    (hreadLo : ∀ j < m, μ (loBase+j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase+j) = hi j)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j)
    (hm : m < 2^W) (hs : |s| ≤ 1) (hx : |x| ≤ U)
    (hf : ∀ j < n, |f j| ≤ U) (hd : d+W+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pRow d [x,b,loBase,hiBase,n,m,dst,powers,W,s] μ (_root_.ThreeSum.LightBandTable.rowTime n W)
      (fun _ μ' =>
        (∀ j < n, μ' (dst+j) = (_root_.ThreeSum.LightBandTable.rowValue lo hi m x s f j : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n) := by sorry
