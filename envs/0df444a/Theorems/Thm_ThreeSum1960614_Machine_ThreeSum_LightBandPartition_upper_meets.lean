-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPartition_upper_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandPartition.upper_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:16.20053+00:00
-- url     : https://prove2.me/theorems/5850b276-5de7-4f34-8567-7570726dd469
-- title:
--   Writing all upper endpoints of a band partition
-- statement:
--   For source values $f$ of length $n$ and positive band size $g$, assume the source precedes the destination, endpoint storage fits memory, addresses fit words, and $n+g+2$ fits a word. The upper-endpoint procedure writes $f(\operatorname{stop}(n,g,i)-1)$ for each band $i$ within the stated time, preserving all cells outside the endpoint array.
--
--   This endpoint contract constructs the upper band bounds consumed by physical owner lookup and normalization.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandPartition.lean#L56-L115

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

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

theorem ThreeSum1960614.Machine.ThreeSum.LightBandPartition.upper_meets {p src dst n g d : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.upperBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hdst : dst+_root_.ThreeSum.BandPartition.size n g ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [src,n,g,dst,_root_.ThreeSum.BandPartition.size n g] μ (_root_.ThreeSum.LightBandPartition.upperTime (_root_.ThreeSum.BandPartition.size n g))
      (fun _ μ' => (∀ i < _root_.ThreeSum.BandPartition.size n g, μ' (dst+i) = f (_root_.ThreeSum.BandPartition.stop n g i-1)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (_root_.ThreeSum.BandPartition.size n g)) := by sorry
