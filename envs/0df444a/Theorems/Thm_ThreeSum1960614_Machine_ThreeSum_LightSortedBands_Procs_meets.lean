-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSortedBands_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:15:43.68141+00:00
-- url     : https://prove2.me/theorems/826f24bb-ce89-4b7e-aced-a985638c0de7
-- title:
--   Correct sorted-band preprocessing from an original list
-- statement:
--   Let an integer list $L$ be stored at the source and let band width $g>0$. Assume ordered source, normalized-value, endpoint-header, and scratch reservations; the stated space and numeric word bounds; address representability; and depth sufficient for normalization and endpoint construction. The procedure produces the exact prepared sorted-band representation of $L$, returns the stored band count, meets its stated time, and preserves cells below scratch outside the three reserved source/value/header regions.
--
--   Builds normalized bands from original values while retaining membership semantics. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSortedBands.lean#L63-L130

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPartition_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNormalize_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightSortedBands
end ThreeSum.LightSortedBands
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightSortedBands
end ThreeSum1960614.Machine.ThreeSum.LightSortedBands

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSortedBands
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs.meets {pMain src values endpoints work g d : ℕ}
    {μ : ℕ → ℤ} {original : List ℤ} (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+original.length ≤ values) (hvalues : values+original.length ≤ endpoints)
    (hendpoints : endpoints+2+2*original.length ≤ work)
    (hspace : _root_.ThreeSum.LightSortedBands.space work original.length ≤ lim.space)
    (hword : ((original.length+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+original.length+Nat.clog 2 original.length+3 ≤ lim.depth)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src original) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,original.length,g,values,endpoints,work] μ (_root_.ThreeSum.LightSortedBands.time original.length)
      (fun r μ' => r = μ' (endpoints+1) ∧ _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared μ' values endpoints g original ∧
        ∀ a, a < work → (a < src ∨ src+original.length ≤ a) →
          (a < values ∨ values+original.length ≤ a) →
          (a < endpoints ∨ endpoints+2+2*original.length ≤ a) → μ' a = μ a) := by sorry
