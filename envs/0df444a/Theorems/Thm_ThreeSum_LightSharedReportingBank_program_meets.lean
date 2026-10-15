-- Prove2me | Theorems.Thm_ThreeSum_LightSharedReportingBank_program_meets
-- name    : ThreeSum.LightSharedReportingBank.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T17:58:14.954302+00:00
-- url     : https://prove2.me/theorems/44e45246-a9fb-43d4-99b5-4fdbf874b095
-- title:
--   Construct the complete reporting bank over occurrences and band pairs
-- statement:
--   Suppose complete retained source banks for arrays of lengths $N_B,N_C$ are stored with local parameters $h,J$, band parameter $g$, and cutoff $2hJ$. Let $N_o$ be the occurrence count, let $b_B,b_C$ be the defined band counts, and put $Q=N_ob_Bb_C$. Choose $0<K\le\lfloor13J/20\rfloor+1$.
--
--   Occurrence rows end before the source header, the source banks end before record base $r_0$, and $5KQ$ record cells end before payload base $a$. Assume $S\le W$, the full payload endpoint and control-word bounds, and the level resource contract for every row at depth $d+2$. Then
--   $$r=a+Q\,\Delta_K,\qquad\text{every occurrence and original band pair has all }K\text{ exact catalogs},$$
--   where $\Delta_K$ is the defined per-pair payload span. Time is $Q(T_{\rm pair}+1000)+300$. Memory below $r_0$, and below $a$ outside the record slab, is preserved.
--
--   This precomputes a shared reporting catalog for every reusable source-pair choice.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingBank.lean#L64-L200

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightSharedReportingPair_program_meets
import Theorems.Thm_ThreeSum_SharedReportingBankRows_Done_append
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_of_kept


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows

theorem ThreeSum.LightSharedReportingBank.program_meets : ∀ {lim : Light.Limits} {μ fB fC : Nat → Int} {header record base NB NC g h J K occ d : Nat} {p shift : Int}
  (H :
    ThreeSum.SourceBandBankData.Stored μ fB fC header NB NC g h J
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
        J)
      occ p shift)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hKpos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) K)
  (hK :
    @LE.le.{0} Nat instLENat K
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightSwitchDepth.depth J)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hocc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightBlockSourceCatalog.count h J)
          J))
      header)
  (hsource :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SourceBandBankData.finish header NB NC g h J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
          J))
      record)
  (hslab :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) K)
          (ThreeSum.SharedReportingBankRows.total h J NB NC g)))
      base)
  (hspace :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SharedReportingBankRows.rowBase base h J K (ThreeSum.SharedReportingBankRows.total h J NB NC g))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSharedReportingBank.controlWord h J K NB NC g)) lim.word)
  (R :
    ∀ (q : Nat),
      @LT.lt.{0} Nat instLTNat q (ThreeSum.SharedReportingBankRows.total h J NB NC g) →
        ThreeSum.LightSharedReportingLevels.Resources lim (ThreeSum.SharedReportingBankRows.rowBase base h J K q) h J K
          g g
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))),
  Light.Meets lim ThreeSum.LightSharedReportingBank.program
    (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBandBankData.first header))
            (@List.cons.{0} Int
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.SourceBandBankLayout.span h J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                    J)))
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBlockSourceCatalog.count h J))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandPartition.size NB g))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandPartition.size NC g))
                    (@List.cons.{0} Int
                      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankLayout.localChoose h))
                      (@List.cons.{0} Int
                        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankLayout.localPairs h))
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt record)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base) (@List.nil.{0} Int)))))))))))))
    μ (ThreeSum.LightSharedReportingBank.time h J K NB NC g) fun (result : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int result
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.SharedReportingBankRows.rowBase base h J K (ThreeSum.SharedReportingBankRows.total h J NB NC g))))
      (And
        (ThreeSum.SharedReportingBankRows.Done ν record base h J K NB NC g
          (ThreeSum.SharedReportingBankRows.total h J NB NC g) fB fC p shift)
        (And (Light.Kept μ ν record)
          (Light.KeptBut μ ν base record
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) K)
              (ThreeSum.SharedReportingBankRows.total h J NB NC g))))) := by
  sorry
