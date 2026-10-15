-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketTest_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:53:12.563787+00:00
-- url     : https://prove2.me/theorems/18e9bdcd-9fd1-4313-b16a-c022b060f0c0
-- title:
--   Execution of independent-flag bucket testing
-- statement:
--   Let original arrays $L,R$ of lengths $N_L,N_R$, key maps $c_L,c_R<M$ and their correct contiguous bucket stores be retained before scratch $w$ in memory $\mu$. Fix residues $r_L,r_R<M$, flags $\phi_L,\phi_R\le1$ and integer A value $a$. Assume addresses fit words, all originals and $a$ fit words, every $a+L_i$ fits a word, $N_LN_R$ fits a word, $w+4$ fits memory and $d+2$ is allowed. Suppose the program contains bucket-test, selector, pair and row bodies. It returns the exact count of original pairs from the flagged residue buckets satisfying $R_j=a+L_i$, within the selected-product time, changing only four scratch cells.
--
--   This checks the original equation while independent endpoint flags restrict each physical fiber.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingBucketTest.lean#L36-L122

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Choose.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketPairs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketSelect_meets
import Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightReportingBucketTest
end ThreeSum.LightReportingBucketTest
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.meets {pMain pSelect pPairs pRow srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : ℕ}
    {μ : ℕ → ℤ}
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.body pSelect pPairs))
    (hselect : P[pSelect]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.body)
    (hpairs : P[pPairs]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.body pRow))
    (hrow : P[pRow]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.body)
    (a : ℤ) (left right : ℕ → ℤ) (keyL keyR : ℕ → ℕ)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyL NL M offsetsL flatL) (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyR NR M offsetsR flatR)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hsrcL : srcL+NL ≤ work) (hsrcR : srcR+NR ≤ work)
    (hoffsetsL : offsetsL+M+1 ≤ work) (hoffsetsR : offsetsR+M+1 ≤ work)
    (hflatL : flatL+NL ≤ work) (hflatR : flatR+NR ≤ work) (hspace : work+4 ≤ lim.space)
    (hkeyL : ∀ i < NL, keyL i<M) (hkeyR : ∀ j < NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i < NL, μ (srcL+i)=left i) (hreadR : ∀ j < NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i < NL, |left i|≤lim.word) (hvaluesR : ∀ j < NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i < NL, |a+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,srcL,srcR,offsetsL,flatL,rL,flagL,offsetsR,flatR,rR,flagR,NL,NR,M,work]
      μ (_root_.ThreeSum.LightReportingBucketTest.time keyL keyR NL NR rL rR flagL flagR)
      (fun r ν => r=(_root_.ThreeSum.ReportingHostBucketTest.testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν work 4) := by sorry
