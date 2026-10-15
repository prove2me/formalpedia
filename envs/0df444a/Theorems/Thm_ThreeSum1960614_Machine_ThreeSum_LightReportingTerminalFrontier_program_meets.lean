-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingTerminalFrontier_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:57:34.096998+00:00
-- url     : https://prove2.me/theorems/0b0a9523-6312-4dc0-9a18-b9fdf3649d3f
-- title:
--   The terminal-frontier program decides the exact physical hit
-- statement:
--   Fix partial depth $k\le J$, an actual prefix list, and a requested prefix count $n$ within its length. Suppose the original source arrays and physical buckets, selected occurrence indices, cover tables, and aligned prefix-mask arrays satisfy their exact read predicates. Assume word-safe values and target sums, pair-count capacity, and the complete ordered terminal-mask, endpoint, flag, and scratch allocation with its depth bound. Procedure 39 returns a Boolean equivalent to the terminal-frontier hit predicate, takes the sum of the actual prefix costs, and preserves memory below the terminal-mask base.
--
--   This terminal theorem sums the costs of the actual retained prefixes and tests original values in their selected physical buckets.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingTerminalFrontier.lean#L40-L151

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
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
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
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

namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightReportingTerminalFrontier
end ThreeSum.LightReportingTerminalFrontier
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier
set_option maxHeartbeats 3800000
set_option maxRecDepth 14000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier.program_meets {μ : ℕ→ℤ}
    {h J k srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR inL inR
      masks masksL masksR base bitBase rowOut work n d : ℕ}
    (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (pres : List (List (Finset (Fin (464*h))))) (hk : k≤J) (hn : n≤pres.length)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i)) NL (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) offsetsL flatL)
    (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right i)) NR (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+n+_root_.ThreeSum.LightReportingTerminalMasks.count h J k+J*(464*h)+10≤lim.depth)
    (hsrcL : srcL+NL≤ masks) (hsrcR : srcR+NR≤ masks)
    (hoffsetsL : offsetsL+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+1≤ masks) (hoffsetsR : offsetsR+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+1≤ masks)
    (hflatL : flatL+NL≤ masks) (hflatR : flatR+NR≤ masks)
    (hocc : occ+J≤ masks) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤ masks)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤ masks)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤ masks)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤ masks)
    (hinL : inL+pres.length≤ masks) (hinR : inR+pres.length≤ masks)
    (hmasks : masks+_root_.ThreeSum.LightReportingTerminalMasks.count h J k≤ masksL) (hmasksL : masksL+_root_.ThreeSum.LightReportingTerminalMasks.count h J k≤ masksR)
    (hmasksR : masksR+_root_.ThreeSum.LightReportingTerminalMasks.count h J k≤base)
    (hstop : _root_.ThreeSum.LightReportingTerminalPreparation.stop base (J*(464*h)) (_root_.ThreeSum.LightReportingTerminalMasks.count h J k)≤bitBase)
    (hbits : bitBase+J*(464*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.space work h J≤lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hreadInL : ∀ i<pres.length, μ (inL+i)=
      (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt pres i))) : ℤ))
    (hreadInR : ∀ i<pres.length, μ (inR+i)=
      (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.prefixAt pres i))) : ℤ))
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |av|≤lim.word) (htarget : ∀ i<NL, |av+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalFrontier.program 39 d
      [av,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,
        occ,maps,candidates,histL,histR,k,_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)),
        inL,inR,masks,masksL,masksR,base,bitBase,rowOut,work,n]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.time p shift left right NL NR q k pres n)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.Hit av p shift left right NL NR q k pres n) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν masks) := by sorry
