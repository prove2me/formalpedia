-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandCandidates_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:19:07.16152+00:00
-- url     : https://prove2.me/theorems/054bf2d2-607a-424c-a543-343ce8653e21
-- title:
--   Constructing all physical band-candidate records
-- statement:
--   Let three band families $A,B,C$ have their exact owner tables stored before destination $o$. Suppose the complete candidate-helper placement, finite space and word requirements, word-sized addresses, and depth allowance hold. The program returns the exact candidate-record count and writes their flattened four-cell records in order, changing only the output record slab within its stated time.
--
--   This constructor converts the computed owner tables into the exact physical records used by scoring and reporting.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandCandidates.lean#L60-L178

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
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
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandCandidateRows_seg_rect
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandCandidatesTable_meets
import Theorems.Thm_ThreeSum_BinarySearch_locate_sound

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightBandCandidates
end ThreeSum.LightBandCandidates
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBandCandidates
end ThreeSum1960614.Machine.ThreeSum.LightBandCandidates

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandCandidates
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidates

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidates.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hsrc : src+_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : _root_.ThreeSum.LightBandCandidates.space dst A.size B.size C.size ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandCandidates.word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ src A B C) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,dst,A.size,B.size,C.size] μ (_root_.ThreeSum.LightBandCandidates.time A.size B.size C.size)
      (fun r ν => r=(_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (4*_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size)) := by sorry
