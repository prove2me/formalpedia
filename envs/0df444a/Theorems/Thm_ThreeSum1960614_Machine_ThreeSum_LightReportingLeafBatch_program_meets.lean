-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingLeafBatch_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:19:56.029513+00:00
-- url     : https://prove2.me/theorems/b10b87c0-b5c3-4008-844b-aebad29055af
-- title:
--   Execution of the exact original-value terminal leaf batch
-- statement:
--   Let original arrays $L,R$ of lengths $N_L,N_R$ have key maps into a positive modulus $M$ and correct retained bucket stores. Let $n$ candidate endpoint hashes $x_i,y_i$, independently Boolean trim flags, and A value $a$ be correctly stored before scratch $w$ in memory $\mu$. Assume all originals, $a$ and $a+L_j$ fit words; endpoint magnitudes are bounded by $U$; $N_LN_R$ fits a word; $w+4+\lfloor\log_2(U+1)\rfloor+2$ fits memory; $4U+4M+16$ fits a word; addresses fit words; and depth $d+n+4$ is allowed. The fixed batch program returns a Boolean, equal to one exactly when one candidate has both flags enabled and matching original-index residue buckets containing an exact equation $R_j=a+L_i$. It meets the specified actual batch time and preserves all cells below $w$.
--
--   This closes terminal reporting against original values without a modular or bucket-search oracle.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingLeafBatch.lean#L69-L156

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingLeaf_program_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightReportingLeafBatch
end ThreeSum.LightReportingLeafBatch
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingLeafBatch
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open scoped _root_.BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program_meets {μ : ℕ→ℤ}
    {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo rawL rawR flagsL flagsR n work U d : ℕ}
    (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyL NL Mo offsetsL flatL) (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyR NR Mo offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+n+4≤lim.depth) (hMo : 0<Mo)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+Mo+1≤work) (hoffsetsR : offsetsR+Mo+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work)
    (hrawL : rawL+n≤work) (hrawR : rawR+n≤work)
    (hflagsL : flagsL+n≤work) (hflagsR : flagsR+n≤work)
    (hspace : work+4+(Nat.log 2 (U+1)+2)≤lim.space)
    (hword : (4*U+4*Mo+16 : ℤ)≤lim.word)
    (hkeyL : ∀ i<NL, keyL i<Mo) (hkeyR : ∀ j<NR, keyR j<Mo)
    (hflagL : ∀ i<n, flagL i≤1) (hflagR : ∀ i<n, flagR i≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hreadXL : ∀ i<n, μ (rawL+i)=xL i) (hreadXR : ∀ i<n, μ (rawR+i)=xR i)
    (hreadFL : ∀ i<n, μ (flagsL+i)=(flagL i : ℤ))
    (hreadFR : ∀ i<n, μ (flagsR+i)=(flagR i : ℤ))
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hxL : ∀ i<n, |xL i|≤(U : ℤ)) (hxR : ∀ i<n, |xR i|≤(U : ℤ))
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program 6 d [a,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,Mo,rawL,rawR,flagsL,flagsR,n,work]
      μ (_root_.ThreeSum.LightReportingLeafBatch.time keyL keyR flagL flagR NL NR Mo U xL xR n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.LightReportingLeafBatch.Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν work) := by sorry
