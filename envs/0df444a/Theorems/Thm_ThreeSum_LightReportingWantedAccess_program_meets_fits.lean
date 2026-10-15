-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedAccess_program_meets_fits
-- name    : ThreeSum.LightReportingWantedAccess.program_meets_fits
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:41:29.182346+00:00
-- url     : https://prove2.me/theorems/a32bfb71-6206-4823-9e53-cc8307108120
-- title:
--   Constant-time access to an owner, its sources, and its shared catalog
-- statement:
--   Fix a stored raw-$A$ incidence array and four-cell owner records for band width $g$, together with consistent source-pair, source-bank, cover-key, and shared-reporting payloads for dimensions $h,J$, source lengths $N_B,N_C$, modulus $p$, and shift. Choose a valid incidence index and occurrence code whose owner's two bands are valid. Assume the value/owner arrays, records, original $B/C$ ranges, and retained payloads end by destination $z$; the occurrence rows end before the bank header. The selector's explicit Fits predicate must bound its headers, stage pointers, fifteen output controls, and intermediate scalars by machine space. Also assume space fits in a word, the selected $A$ value fits in a word, and the current depth is below the limit. Then the accessor runs within $8100$ steps and returns
--   $$
--   r=z,\qquad \nu[z:z+20]=\operatorname{record}(\text{incidence},\text{occurrence}),\qquad
--   \forall a<z,\ \nu(a)=\mu(a).
--   $$
--   The record contains the $A$ value, owner and band indices, shared-catalog pointer, and fifteen source controls. It supplies the guarded reporter's concrete inputs.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedAccess.lean#L56-L153

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum_LightReportingOwnerSelect_program_meets
import Theorems.Thm_ThreeSum_LightReportingSourceSelect_program_meets_fits
import Theorems.Thm_ThreeSum_LightSharedReportingLookup_program_meets
import Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_of_kept
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_of_kept
import Theorems.Thm_ThreeSum_SourceBandPairData_Stored_of_kept


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightReportingWantedAccess.program_meets_fits : ∀ {lim : Light.Limits} {μ fA fB fC : Nat → Int}
  {n g vals owners positions records idx pair bank cover NB NC p h J cut occ code srcB srcC report dst d : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record} {shift : Int}
  (HA : ThreeSum.BandRawA.Stored μ vals owners positions fA (ThreeSum.BandRawA.items n g rs))
  (HR : Light.Seg μ records (ThreeSum.BandCandidateRows.cells rs))
  (hidx : @LT.lt.{0} Nat instLTNat idx (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
  (HP : ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (ThreeSum.BlockSourceEncoding.modulus h J) shift)
  (HB : ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (@Nat.cast.{0} Int instNatCastInt p) shift)
  (HC : ThreeSum.LightCoverKeyData.Stored μ cover h J)
  (HQ : ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (@Nat.cast.{0} Int instNatCastInt p) shift)
  (hi : @LT.lt.{0} Nat instLTNat (ThreeSum.BandRawA.ownerRecord n g rs idx).b (ThreeSum.BandPartition.size NB g))
  (hj : @LT.lt.{0} Nat instLTNat (ThreeSum.BandRawA.ownerRecord n g rs idx).c (ThreeSum.BandPartition.size NC g))
  (hk : @LT.lt.{0} Nat instLTNat code (ThreeSum.LightBlockSourceCatalog.count h J))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hvals :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) vals
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      dst)
  (howners :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) owners
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      dst)
  (hrecords :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) records
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      dst)
  (hsrcB : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB NB) dst)
  (hsrcC : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC NC) dst)
  (hpair :
    @LE.le.{0} Nat instLENat (ThreeSum.SourceBandPairData.next pair NB NC g (ThreeSum.BlockSourceEncoding.modulus h J))
      dst)
  (hbank : @LE.le.{0} Nat instLENat (ThreeSum.SourceBandBankData.finish bank NB NC g h J cut) dst)
  (hocc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightBlockSourceCatalog.count h J)
          J))
      bank)
  (hcover : @LE.le.{0} Nat instLENat (ThreeSum.LightCoverKeyData.keyEnd cover h J) dst)
  (hreport : @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankHeader.finish report h J NB NC g) dst)
  (hspace :
    ThreeSum.ReportingHostSourceSelection.Fits
      (ThreeSum.LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code) pair bank cover
      srcB srcC (ThreeSum.BandRawA.ownerRecord n g rs idx).b (ThreeSum.BandRawA.ownerRecord n g rs idx).c code J
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      lim.space)
  (hvalue :
    @LE.le.{0} Int Int.instLEInt
      (@abs.{0} Int instLatticeInt Int.instAddGroup (fA (ThreeSum.BandRawA.labelAt n g rs idx).position)) lim.word),
  Light.Meets lim ThreeSum.LightReportingWantedAccess.program
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt vals)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt owners)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt records)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt idx)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pair)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bank)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcC)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt code)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt report)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))))))))))
    μ (@OfNat.ofNat.{0} Nat (nat_lit 8100) (instOfNatNat (nat_lit 8100))) fun (result : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int result (@Nat.cast.{0} Int instNatCastInt dst))
      (And
        (Light.Seg ν dst
          (ThreeSum.LightReportingWantedAccess.record fA n g rs idx pair bank cover NB NC h J cut occ code srcB srcC
            report))
        (Light.Kept μ ν dst)) := by
  sorry
