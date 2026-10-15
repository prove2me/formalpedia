-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedDecodeAccess_program_meets_fits
-- name    : ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:29:05.921978+00:00
-- url     : https://prove2.me/theorems/57c592ec-32c6-4028-a533-2aad51c2b645
-- title:
--   Decoding a wanted pair and selecting its retained reporting record
-- statement:
--   Let $N$ be the length of the retained A-incidence list, and suppose a physical pair slot contains $(i,j)$ with $i<3N$, $j<(TM)^J$, and $i,j\le V$. Here $T$ is the local schedule length and $M$ the retained output-layer size. Assume exact stored A values, owners and positions, owner records, source-band pairs and banks, cover keys, shared reporting headers, and the layer-mask table. The owner selected by $i\bmod N$ has valid B and C band indices.
--
--   All retained inputs end before decoding base $e$, the occurrence table ends before its bank, $e+4+2J\le a$, and $a+20\le w$. Assume the decoder's stated space/word bounds, the source selector's individual address and scalar bounds, $S\le W$, $d+4<D$, and a word-bounded selected A value.
--
--   The fixed routine returns $a$ and stores
--   $$[i\bmod N,\lfloor i/N\rfloor,j,\operatorname{occurrenceCode}(j)]$$
--   plus the two decoded block rows at $e$, and the exact twenty-cell owner/source/catalog record at $a$. It preserves cells below $e$ and takes at most $J(200\lambda+700)+100\lambda+8880$ steps, where $\lambda=\lfloor\log_2(V+1)\rfloor$.
--
--   This connects an emitted pair slot to its retained reporting inputs.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedDecodeAccess.lean#L46-L127

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
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Theorems.Thm_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum_LightReportingWantedAccess_program_meets_fits
import Theorems.Thm_ThreeSum_LightWantedDecode_meets
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
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightReportingWantedAccess
end ThreeSum.LightReportingWantedAccess
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits : ∀ {lim : Light.Limits} {μ fA fB fC : Nat → Int}
  {n g vals owners positions records pair bank cover NB NC p h J cut occ srcB srcC report decoded dst work d pairs slot
    i j V masks : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record} {shift : Int}
  (HA : ThreeSum.BandRawA.Stored μ vals owners positions fA (ThreeSum.BandRawA.items n g rs))
  (HR : Light.Seg μ records (ThreeSum.BandCandidateRows.cells rs))
  (hiRaw :
    @LT.lt.{0} Nat instLTNat i
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))))
  (hjKey :
    @LT.lt.{0} Nat instLTNat j
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.OutputDecodeRecords.localCount h) J))
  (hiV : @LE.le.{0} Nat instLENat i V) (hjV : @LE.le.{0} Nat instLENat j V)
  (HP : ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (ThreeSum.BlockSourceEncoding.modulus h J) shift)
  (HB : ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (@Nat.cast.{0} Int instNatCastInt p) shift)
  (HC : ThreeSum.LightCoverKeyData.Stored μ cover h J)
  (HQ : ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (@Nat.cast.{0} Int instNatCastInt p) shift)
  (hi :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))).b
      (ThreeSum.BandPartition.size NB g))
  (hj :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))).c
      (ThreeSum.BandPartition.size NC g))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.depth)
  (hvals :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) vals
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      decoded)
  (howners :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) owners
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      decoded)
  (hpositions :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) positions
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      decoded)
  (hrecords :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) records
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      decoded)
  (hsrcB : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB NB) decoded)
  (hsrcC : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC NC) decoded)
  (hpair :
    @LE.le.{0} Nat instLENat (ThreeSum.SourceBandPairData.next pair NB NC g (ThreeSum.BlockSourceEncoding.modulus h J))
      decoded)
  (hbank : @LE.le.{0} Nat instLENat (ThreeSum.SourceBandBankData.finish bank NB NC g h J cut) decoded)
  (hocc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightBlockSourceCatalog.count h J)
          J))
      bank)
  (hcover : @LE.le.{0} Nat instLENat (ThreeSum.LightCoverKeyData.keyEnd cover h J) decoded)
  (hreport : @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankHeader.finish report h J NB NC g) decoded)
  (hdecoded :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) decoded
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          J)
        J)
      dst)
  (hwork :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
      work)
  (hpairs :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pairs
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      decoded)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks
        (ThreeSum.OutputDecodeRecords.layerCount h))
      decoded)
  (hleft :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pairs
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot)))
      (@Nat.cast.{0} Int instNatCastInt i))
  (hright :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pairs
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt j))
  (hread :
    ∀ (s : Nat),
      @LT.lt.{0} Nat instLTNat s (ThreeSum.OutputDecodeRecords.layerCount h) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks s))
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.LocalMaskGraph.maskAt
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
              s)))
  (hdecoderSpace : @LE.le.{0} Nat instLENat (ThreeSum.LightWantedDecode.space work V) lim.space)
  (hdecoderWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightWantedDecode.word V (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) h
          J))
      lim.word)
  (hspace :
    ThreeSum.ReportingHostSourceSelection.Fits
      (ThreeSum.LightReportingWantedAccess.selection n g rs
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
        pair bank cover NB NC h J cut occ
        (ThreeSum.OutputDecodeOccurrenceCode.code (ThreeSum.GlobalEncoding.scheduleSize h)
          (ThreeSum.OutputDecodeRecords.layerCount h) J j))
      pair bank cover srcB srcC
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))).b
      (ThreeSum.BandRawA.ownerRecord n g rs
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))).c
      (ThreeSum.OutputDecodeOccurrenceCode.code (ThreeSum.GlobalEncoding.scheduleSize h)
        (ThreeSum.OutputDecodeRecords.layerCount h) J j)
      J
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      lim.space)
  (hvalue :
    @LE.le.{0} Int Int.instLEInt
      (@abs.{0} Int instLatticeInt Int.instAddGroup
        (fA
          (ThreeSum.BandRawA.labelAt n g rs
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
                (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))).position))
      lim.word),
  Light.Meets lim ThreeSum.LightReportingWantedDecodeAccess.program
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pairs)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt slot)
        (@List.cons.{0} Int
          (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.GlobalEncoding.scheduleSize h))
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.OutputDecodeRecords.layerCount h))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt decoded)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt vals)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt owners)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt records)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pair)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bank)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcC)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt report)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                                          (@List.nil.{0} Int))))))))))))))))))))
    μ (ThreeSum.LightReportingWantedDecodeAccess.time J V) fun (result : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int result (@Nat.cast.{0} Int instNatCastInt dst))
      (And
        (ThreeSum.LightWantedDecode.Stored ν decoded
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)) h J i j)
        (And
          (Light.Seg ν dst
            (ThreeSum.LightReportingWantedAccess.record fA n g rs
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
                (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
              pair bank cover NB NC h J cut occ
              (ThreeSum.OutputDecodeOccurrenceCode.code (ThreeSum.GlobalEncoding.scheduleSize h)
                (ThreeSum.OutputDecodeRecords.layerCount h) J j)
              srcB srcC report))
          (Light.Kept μ ν decoded))) := by
  sorry
