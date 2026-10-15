-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorWantedSources_program_meets
-- name    : ThreeSum.LightEncodedColorWantedSources.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T18:13:24.363936+00:00
-- url     : https://prove2.me/theorems/a38adc09-7c53-49ae-8bf7-96cebde6d879
-- title:
--   Construct wanted pairs and finite source banks in one encoded stage
-- statement:
--   Let $n,p,M>0$. Memory below free base $f$ contains a list $X$ bounded by $U$ and a normalized colored-band payload for original lists of length at most $n$; the original $B,C$ values are also bounded by $U$. Use the prescribed micro-half $h_n$, block count $J_n$, band size, and source cutoff.
--
--   Assume $S\le W$ and the combined wanted/source space, word, and depth budgets. The routine constructs the actual cover and global key data, selects offset $\delta$, materializes the wanted pairs, and constructs the finite source banks at the following source base. If $N_w$ is the stored wanted-pair count and $N_q$ the global key count, then
--   $$M N_w\le3|X|N_q.$$
--   It retains the exact lifted-key list for $X$, normalized payload, cover data, and wanted output, returns the source finish address, and preserves memory below $f$. Time is guarded wanted construction plus the uniform encoded-source budget plus $400$.
--
--   This supplies both the balanced wanted list and its corresponding concrete source banks.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorWantedSources.lean#L43-L117

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Theorems.Thm_ThreeSum_LightEncodedColorFiniteSources_program_meets
import Theorems.Thm_ThreeSum_LightGuardedWanted_program_meets
import Theorems.Thm_ThreeSum_SourceFiniteData_Normalized_keep


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightEncodedColorWantedSources.program_meets : ∀ {lim : Light.Limits} {d : Nat} {μ : Nat → Int} {a free av ae bv be cv ce tables rec vals n p U M : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  {originalA originalB originalC A B C xs : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C} {rA : Int}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (ThreeSum.LightEncodedColorWantedSources.depth n M (@List.length.{0} Int xs)))
      lim.depth)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hA : @LE.le.{0} Nat instLENat (@List.length.{0} Int originalA) n)
  (hB : @LE.le.{0} Nat instLENat (@List.length.{0} Int originalB) n)
  (hC : @LE.le.{0} Nat instLENat (@List.length.{0} Int originalC) n)
  (ha :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a (@List.length.{0} Int xs)) free)
  (hav : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) av n) free)
  (hae :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ae
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      free)
  (hbv : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv n) free)
  (hbe :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      free)
  (hcv : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv n) free)
  (hce :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      free)
  (htables :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) tables
        (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n)))
      free)
  (hrecords :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rec
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n))))
      free)
  (hcatalog :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightBandRawA.space vals (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n))
        (ThreeSum.BandScales.bandSize n))
      free)
  (hspace : @LE.le.{0} Nat instLENat (@ThreeSum.LightEncodedColorWantedSources.space free n p M U inst xs) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightEncodedColorWantedSources.word n p M U (@List.length.{0} Int xs)))
      lim.word)
  (hread : Light.Seg μ a xs)
  (hvalues :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U))
  (hboundB :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalB z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U))
  (hboundC :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalC z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U))
  (H :
    ThreeSum.SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals (ThreeSum.BandScales.bandSize n)
      (ThreeSum.BandScales.bandSize_pos n) originalA originalB originalC A B C hsA hsB hsC rA),
  Light.Meets lim ThreeSum.LightEncodedColorWantedSources.program
    (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) d
    (ThreeSum.LightEncodedColorWantedSources.args a free bv be cv ce n p M (@List.length.{0} Int xs)) μ
    (@ThreeSum.LightEncodedColorWantedSources.time n p M U inst xs) fun (r : Int) (ν : Nat → Int) =>
    And
      (ThreeSum.SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals (ThreeSum.BandScales.bandSize n)
        (ThreeSum.BandScales.bandSize_pos n) originalA originalB originalC A B C hsA hsB hsC rA)
      (And
        (ThreeSum.SourceFiniteData.Stored ν (@ThreeSum.LightEncodedColorFiniteSources.base free n p M inst xs)
          (ThreeSum.BandScales.bandSize n) p (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
          (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) (ThreeSum.Scales.mu n) B C
          (@Nat.cast.{0} Int instNatCastInt
            (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt p) xs
              (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
              (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))))
          r)
        (And
          (ThreeSum.LightCoverKeyData.Stored ν free (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
            (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
          (And
            (ThreeSum.LightWantedSetup.Output ν
              (ThreeSum.LightGuardedWanted.wantedFree free (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) (@List.length.{0} Int xs))
              M (ThreeSum.LightGuardedWanted.left p xs)
              (ThreeSum.LightGuardedWanted.right (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
              (ThreeSum.LightGuardedWanted.totalKeys (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
              (@Nat.cast.{0} Int instNatCastInt
                (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt p) xs
                  (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                  (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))))
            (And
              (@LE.le.{0} Nat instLENat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) M
                  (ν
                      (ThreeSum.LightGuardedWanted.wantedFree free
                        (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                        (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) (@List.length.{0} Int xs))).toNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
                  (ThreeSum.LightGuardedWanted.totalKeys (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                    (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))))
              (And
                (Light.Seg ν
                  (ThreeSum.LightCoverKeyData.keyEnd free (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                    (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
                  (ThreeSum.RawAKeyLists.keys (@Nat.cast.{0} Int instNatCastInt p) xs))
                (Light.Kept μ ν free)))))) := by
  sorry
