-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightGlobalKeys_Procs_meets_with_masks
-- name    : ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs.meets_with_masks
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:20:41.435461+00:00
-- url     : https://prove2.me/theorems/3f9fd579-f18e-4619-9b7f-2ce32448baa6
-- title:
--   Execution of global keys with retained local masks
-- statement:
--   Let $h,J\in\mathbb N$, selected-map base $a$, free base $f$, and $\lambda,P,d,\mu$ limits, program, depth and memory be given. Suppose the program’s literal closure record identifies global-key construction and all callees. The selected-map rows in memory are exactly the original occurrence-indexed false/true coefficients; they end before $f$. Assume addresses fit words, the explicit global-key space/word budgets fit and $d+464h+J+5$ is allowed. The procedure writes every local output-layer mask at $f$, builds the ordered global-key list, precedes it by count $N(h)^J$, and returns that count-cell address. It meets its prescribed time and preserves every cell below $f$.
--
--   This retains both keys and local masks needed to decode the same original global output records later.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightGlobalKeys.lean#L90-L183

import Aesop
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_GlobalKeyEnumeration_rawOutput_abs_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalKeys_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixKeys_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalKeyArraySemantics_seg_flatMap_rows
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightGlobalKeys
end ThreeSum.LightGlobalKeys
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
end ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs.meets_with_masks {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*h+J+5 ≤ lim.depth)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.space free h J ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J : ℤ) ≤ lim.word)
    (hmaps : maps+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ free)
    (hreadFalse : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ i < 464*h,
      μ (maps+j*(2*(464*h))+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ i < 464*h,
      μ (maps+j*(2*(464*h))+464*h+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true j i : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [464*h,2*h,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,J,maps,
      _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.time h J)
      (fun r ν => r=((_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J : ℕ) : ℤ) ∧
        ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J)=((_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J+1) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J) ∧
        (∀ i < _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h,
          ν (free+i)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by sorry
