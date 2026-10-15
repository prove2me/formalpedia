-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPartition_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandPartition.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:53:18.408069+00:00
-- url     : https://prove2.me/theorems/5b8452c9-19cc-43a8-899f-67490e84cbd9
-- title:
--   Constructing both endpoints of every band
-- statement:
--   For a stored length-$n$ integer array $f$ and positive band size $g$, assume quotient, lower-endpoint, and upper-endpoint helpers are installed, source precedes destination, $2n$ output cells fit, $n+g+2$ and addresses fit words, and one call level is available. The program returns the exact band count and writes each lower endpoint $f(\operatorname{start}(g,i))$ and upper endpoint $f(\operatorname{stop}(n,g,i)-1)$ in its stated time.
--
--   This partition contract computes both physical endpoints rather than assuming access to abstract band boundaries.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandPartition.lean#L130-L177

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPartition_upper_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightBandPartition
end ThreeSum.LightBandPartition
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPartition
end ThreeSum1960614.Machine.ThreeSum.LightBandPartition

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandPartition.meets {pMain pDivide pLower pUpper src dst n g d : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.body pDivide pLower pUpper))
    (hdiv : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hlower : P[pLower]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.lowerBody) (hupper : P[pUpper]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.upperBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hspace : dst+2*n ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hd : d+1 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,g,dst] μ (_root_.ThreeSum.LightBandPartition.time n g)
      (fun r μ' => r = (_root_.ThreeSum.BandPartition.size n g : ℤ) ∧
        (∀ i < _root_.ThreeSum.BandPartition.size n g, μ' (dst+i) = f (_root_.ThreeSum.BandPartition.start g i)) ∧
        (∀ i < _root_.ThreeSum.BandPartition.size n g, μ' (dst+n+i) = f (_root_.ThreeSum.BandPartition.stop n g i-1)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (2*n)) := by sorry
