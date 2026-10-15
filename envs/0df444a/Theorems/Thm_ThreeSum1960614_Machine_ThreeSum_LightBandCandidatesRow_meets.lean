-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandCandidatesRow_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:08:45.773+00:00
-- url     : https://prove2.me/theorems/31bb7386-da45-4a18-b683-198d3f3186a7
-- title:
--   Constructing a full row of band-candidate records
-- statement:
--   Suppose the row and mode-specific cell bodies are installed. A stored length-$n$ source $f$, outer index, and each source value are bounded by $U$; source precedes the four-cell-per-record destination, the destination fits, addresses fit words, $U+10$ fits a word, and one call level is available. The row call writes each $\operatorname{make}(\mathrm{mode},\mathrm{outer},j,f(j))$ and changes only the $4n$ destination cells, within its declared time.
--
--   This row contract builds the literal physical candidate records used by the later owner-table and scoring stages.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandCandidatesRow.lean#L29-L76

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandCandidatesCell_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.LightBandCandidatesRow
end ThreeSum.LightBandCandidatesRow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow
end ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandCandidatesRow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst n outer U : ℕ} {f : ℕ → ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow.meets {pMain pCell : ℕ} (mode : _root_.ThreeSum.BandCandidateRows.Mode)
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesRow.body pCell))
    (hcell : P[pCell]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandCandidatesCell.body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+n ≤ dst) (hspace : dst+4*n ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word)
    (hn : n ≤ U) (houter : outer ≤ U)
    (hf : ∀ j < n, f j ≤ U) (hread : ∀ j < n, μ (src+j)=(f j : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,dst,n,outer] μ (_root_.ThreeSum.LightBandCandidatesRow.time n)
      (fun _ ν =>
        (∀ j < n, _root_.ThreeSum1960614.Machine.Light.Seg ν (dst+4*j) (_root_.ThreeSum.BandCandidateRows.make mode outer j (f j)).cells) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (4*n)) := by sorry
