-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandRawACatalog_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:26:48.693957+00:00
-- url     : https://prove2.me/theorems/5a0c1f2e-97ec-4dff-9439-a12b097ff32b
-- title:
--   Execution of the complete A-incidence owner catalog
-- statement:
--   Let $A,B,C$ be band-enumeration families, $n_A,n_B,n_C$ original lengths and $g>0$ a band size, with $A$ having the prescribed number of A bands. Suppose memory stores their exact band headers, owner lookup tables and original A-value map $f$. Tables, source and all three two-cell headers end before the record base; the four-cell owner-record output ends before the parallel A-incidence arrays. Let $\lambda,P,d$ be limits, program and depth, with a literal closure record for this catalog constructor. Assume addresses fit words, its exact space/word budgets fit and $d+3$ is strictly below the depth limit. It writes the exact owner records and parallel value, owner-slot and sorted-position arrays for every flagged A incidence, returns their total count, meets its stated time and preserves memory below the record base.
--
--   This constructs the actual owner-labeled A domain consumed by wanted generation and original-value reporting.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandRawACatalog.lean#L50-L125

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
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
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Data.List.Dedup
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
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandCandidates_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandRawA_Procs_meets
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.LightBandRawACatalog
end ThreeSum.LightBandRawACatalog
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog
end ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandRawACatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
set_option maxHeartbeats 2100000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawACatalog.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hA : A.size=_root_.ThreeSum.BandPartition.size nA g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth) (hg : 0 < g)
    (htable : tables+_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size ≤ rec)
    (hsrc : src+nA ≤ rec) (hheadA : headerA+2 ≤ rec)
    (hheadB : headerB+2 ≤ rec) (hheadC : headerC+2 ≤ rec)
    (hrec : rec+4*_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size ≤ vals)
    (hspace : _root_.ThreeSum.LightBandRawACatalog.space vals A.size B.size C.size g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandRawACatalog.word nA A.size B.size C.size g : ℤ) ≤ lim.word)
    (hheaderA : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ headerA nA A)
    (hheaderB : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ headerB nB B)
    (hheaderC : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ headerC nC C)
    (htables : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ tables A B C)
    (hread : ∀ j < nA, μ (src+j)=f j) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [tables,rec,src,headerA,headerB,headerC,g,vals]
      μ (_root_.ThreeSum.LightBandRawACatalog.time A.size B.size C.size g)
      (fun r ν => r=((_root_.ThreeSum.BandRawA.items nA g (_root_.ThreeSum.BandCandidateRows.records A B C)).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν rec (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored ν vals (_root_.ThreeSum.LightBandRawA.ownerBase vals (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
          (_root_.ThreeSum.LightBandRawA.positionBase vals (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
          f (_root_.ThreeSum.BandRawA.items nA g (_root_.ThreeSum.BandCandidateRows.records A B C)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν rec) := by sorry
