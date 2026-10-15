-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedDecodeAccess_program_meets_fits
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:53:25.68847+00:00
-- url     : https://prove2.me/theorems/1917668d-13c8-43e5-9928-9eb4bc416b2e
-- title:
--   Decoding a wanted pair and selecting its retained data
-- statement:
--   Suppose memory stores the packed original-$A$ incidences and owner records, both original-source catalogs, occurrence banks, local cover keys, and shared reporting bank. Let one actual pair slot contain valid left and right indices bounded by $V$, with valid owner band indices. Assume every persistent region and the layer-mask list ends before the decoded record; that record precedes the twenty-cell access record and scratch; the decoder word/space and selector-fit conditions hold; the selected original value fits a word; and addresses and five call levels are available. The closed program constructs the exact decoded label record and retained access record, returns its destination, and preserves all earlier data within its stated time.
--
--   Connects one physical emitted pair directly to original source values and shared catalogs. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWantedDecodeAccess.lean#L46-L127

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
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
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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

namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
end ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.LightReportingWantedAccess
end ThreeSum.LightReportingWantedAccess
namespace ThreeSum.LightReportingWantedDecodeAccess
end ThreeSum.LightReportingWantedDecodeAccess
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingWantedDecodeAccess
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum.LightReportingWantedAccess
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
set_option linter.unusedVariables false

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n g vals owners positions records pair bank cover NB NC p h J cut occ srcB srcC report decoded dst work d : ℕ}
    {pairs slot i j V masks : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
    (HA : _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ vals owners positions fA (_root_.ThreeSum.BandRawA.items n g rs))
    (HR : _root_.ThreeSum1960614.Machine.Light.Seg μ records (_root_.ThreeSum.BandCandidateRows.cells rs)) (hiRaw : i<3*(_root_.ThreeSum.BandRawA.items n g rs).length)
    (hjKey : j<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (hiV : i≤V) (hjV : j≤V)
    (HP : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift)
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (p : ℤ) shift)
    (HC : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover h J)
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).c<_root_.ThreeSum.BandPartition.size NC g)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hvals : vals+(_root_.ThreeSum.BandRawA.items n g rs).length≤decoded)
    (howners : owners+(_root_.ThreeSum.BandRawA.items n g rs).length≤decoded)
    (hpositions : positions+(_root_.ThreeSum.BandRawA.items n g rs).length≤decoded)
    (hrecords : records+4*rs.length≤decoded)
    (hsrcB : srcB+NB≤decoded) (hsrcC : srcC+NC≤decoded)
    (hpair : _root_.ThreeSum.SourceBandPairData.next pair NB NC g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)≤decoded)
    (hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bank NB NC g h J cut≤decoded)
    (hocc : occ+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J≤decoded)
    (hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish report h J NB NC g≤decoded)
    (hdecoded : decoded+4+J+J≤dst) (hwork : dst+20≤work)
    (hpairs : pairs+2*slot+2≤decoded) (hmasks : masks+_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h≤decoded)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,
      μ (masks+s)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) s : ℤ))
    (hdecoderSpace : _root_.ThreeSum.LightWantedDecode.space work V≤lim.space)
    (hdecoderWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word V (_root_.ThreeSum.BandRawA.items n g rs).length h J : ℤ)≤lim.word)
    (hspace : _root_.ThreeSum.ReportingHostSourceSelection.Fits
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length) pair bank cover NB NC h J cut occ
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j))
      pair bank cover srcB srcC
      (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).b
      (_root_.ThreeSum.BandRawA.ownerRecord n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).c
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j) J (dst+5) lim.space)
    (hvalue : |fA (_root_.ThreeSum.BandRawA.labelAt n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length)).position|≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program 9 d
      [pairs,slot,(_root_.ThreeSum.BandRawA.items n g rs).length,J,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,masks,decoded,work,
        vals,owners,records,pair,bank,cover,srcB,srcC,report,dst]
      μ (_root_.ThreeSum.LightReportingWantedDecodeAccess.time J V)
      (fun result ν => result=(dst : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored ν decoded (_root_.ThreeSum.BandRawA.items n g rs).length h J i j ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.record fA n g rs (i%(_root_.ThreeSum.BandRawA.items n g rs).length) pair bank cover NB NC h J cut occ
          (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j) srcB srcC report) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν decoded) := by sorry
