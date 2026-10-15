-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceRetainedStages_meets_right
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_right
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:34:21.518056+00:00
-- url     : https://prove2.me/theorems/93e47cfe-0b06-49fd-8612-3b6332db19ca
-- title:
--   Right source stages from a retained original-input histogram
-- statement:
--   Let a finite source set $B$ with integer values be enumerated by $N$ actual array positions, preserving values. Fix local scale $h$, block count $J$, global output $q$, integer shift, prime control $p$, and cutoff at most $464hJ$. Suppose memory stores the exact right endpoint array, independent right flags, and retained histogram for those original values. Under the concrete retained-stage interface, ordered data/mask/scratch reservations, and stated word, address, space, and depth bounds, the procedure constructs every specified right-source zeta stage in its stated time and preserves memory before the stage base.
--
--   Reuses a once-built original histogram to construct exact source transforms. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L90-L125

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockIndex_maskHash_right
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRetainedStages_Procs_meets
import Theorems.Thm_ThreeSum_OneHotMask_eval_le

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.LightBlockSourceRetainedStages
end ThreeSum.LightBlockSourceRetainedStages
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBlockSourceRetainedStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_right {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J N raw flags p table base work cut maskBase : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+8 ≤ lim.depth)
    (hcut : cut ≤ J*(464*h))
    (hraw : raw+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ base)
    (hflags : flags+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ base)
    (htable : table+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hdata : base+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ work)
    (hspace : _root_.ThreeSum.LightSourceRetainedStages.space work (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) N : ℤ) ≤ lim.word)
    (hinput : ∀ i : Fin N, v i.val = b (e i))
    (hhistRead : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J, μ (table+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift v N r : ℤ))
    (hrawRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,
      μ (raw+i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,
      μ (flags+i) = (if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [raw,flags,table,base,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,work,J*(464*h),cut,maskBase,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut]
      μ (_root_.ThreeSum.LightSourceRetainedStages.time (J*(464*h)) cut (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J))
      (fun _ ν => _root_.ThreeSum.LightZetaStages.StoredThrough ν base cut
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(464*h)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by sorry
