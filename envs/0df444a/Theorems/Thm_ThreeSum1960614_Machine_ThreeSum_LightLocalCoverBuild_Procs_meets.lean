-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverBuild_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:42:50.722133+00:00
-- url     : https://prove2.me/theorems/c82c0a51-3920-4a9a-bd9d-65117ce4359e
-- title:
--   Execution of the complete deterministic local-cover builder
-- statement:
--   Let $h\in\mathbb N$. Reserve, in order, the local layer masks, Boolean bit rows, all radix-enumerated candidate coefficients, two raw arrays, two candidate bucket-histogram arrays, support matrix, greedy workspace and selected schedule coefficients. Let the dimensions be the exact local vertex/candidate/column/schedule counts at width $464h$. Suppose every listed reservation ends before the next, the greedy workspace ends before selected coefficients, the latter fit memory, and the exact candidate scratch and cover word bounds fit. For Light limits/program/depth $\lambda,P,d$, assume addresses fit words, $d+464h+7$ is allowed and the literal procedure closure holds. The builder returns the selected-coefficient base, establishes the exact candidate data and occurrence-indexed schedule rows, stores each selected candidate index, meets its prescribed time and preserves all cells below the mask base.
--
--   This executes the original deterministic local cover without assuming chosen maps, masks or support tables.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalCoverBuild.lean#L51-L138

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
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
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.Range
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

namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable
end ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverBuild
end ThreeSum.LightLocalCoverBuild
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.Procs P pMain)
    {μ : ℕ → ℤ} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*h+7 ≤ lim.depth)
    (hspace : _root_.ThreeSum.LightLocalCoverCandidate.space work (464*h)
      (_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ lim.space)
    (hmasks : masks+_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h ≤ bitPtr)
    (hbits : bitPtr+_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h*(464*h) ≤ maps)
    (hmaps : maps+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*(2*(464*h)) ≤ raw0)
    (hraw0 : raw0+2*_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h ≤ raw1)
    (hraw1 : raw1+2*_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h ≤ hist0)
    (hhist0 : hist0+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ hist1)
    (hhist1 : hist1+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ matrixPtr)
    (hmatrix : matrixPtr+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h ≤ work)
    (hschedule : work+_root_.ThreeSum.LightCoverGreedy.total (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.word h : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h,_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,
        masks,bitPtr,maps,raw0,raw1,hist0,hist1,matrixPtr,work,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,scheduleMaps]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.time h)
      (fun r ν => r = (scheduleMaps : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data ν h maps hist0 hist1 matrixPtr ∧ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows ν h scheduleMaps ∧
        (∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
          ν (_root_.ThreeSum.LightCoverGreedy.out work (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν masks) := by sorry
