-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandTable_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:12:42.04123+00:00
-- url     : https://prove2.me/theorems/5574c6a5-c349-4620-844e-28f5f7305dd5
-- title:
--   Constructing the full band-lookup matrix
-- statement:
--   Let stored integer arrays $f,g$ have lengths $n_X,n_Y$ and values bounded by $U$. Let stored endpoint arrays of length $m$ have nondecreasing lower endpoints, with $m<2^W$, and let a width-$W$ power table be stored. Under the ordered layout, sign $|s|\le1$, word, query, helper, and depth bounds, the table procedure writes every semantic lookup row value at row-major offset $in_Y+j$, changing only the matrix destination within its stated time.
--
--   This matrix contract supplies every actual pairwise band lookup used by the owner-record enumeration.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandTable.lean#L116-L206

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandTable_row_meets

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

theorem ThreeSum1960614.Machine.ThreeSum.LightBandTable.meets {pMain pRow pLookup pSearch a b loBase hiBase nX nY m dst powers W d U : ℕ}
    {s : ℤ} (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.body pRow))
    (hrow : P[pRow]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandTable.rowBody pLookup))
    (hlookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f g lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nX ≤ dst) (hb : b+nY ≤ dst)
    (hlo : loBase+m ≤ dst) (hhi : hiBase+m ≤ dst)
    (hdst : dst+nX*nY ≤ powers) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hqueryWord : 2*(U : ℤ) ≤ lim.word)
    (hreadA : ∀ i < nX, μ (a+i) = f i)
    (hreadB : ∀ j < nY, μ (b+j) = g j)
    (hreadLo : ∀ j < m, μ (loBase+j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase+j) = hi j)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j)
    (hm : m < 2^W) (hs : |s| ≤ 1)
    (hf : ∀ i < nX, |f i| ≤ U) (hg : ∀ j < nY, |g j| ≤ U)
    (hd : d+W+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s] μ (_root_.ThreeSum.LightBandTable.time nX nY W)
      (fun _ μ' =>
        (∀ i < nX, ∀ j < nY,
          μ' (dst+i*nY+j) = (_root_.ThreeSum.LightBandTable.rowValue lo hi m (f i) s g j : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (nX*nY)) := by sorry
