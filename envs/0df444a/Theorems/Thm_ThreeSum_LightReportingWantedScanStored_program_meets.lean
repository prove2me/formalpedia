-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedScanStored_program_meets
-- name    : ThreeSum.LightReportingWantedScanStored.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T18:51:03.387076+00:00
-- url     : https://prove2.me/theorems/7cacdc5f-46a4-4c9e-9543-2da524dbf68d
-- title:
--   Scan the physical wanted array with exact early-stop counter semantics
-- statement:
--   Suppose a complete reporting payload for bounded input $|x_i|\le U$ is stored, with selected $p>0$ and $4p\le M$, where $M$ is the global modulus. Let $N$ be its wanted-slot count, $m_i$ the root reporting mass of physical slot $i$, $H_i$ its terminal original-value hit predicate, and $P(k)=\sum_{i<k}m_i$. The initialized threshold is $\theta=\operatorname{representationCap}\cdot\operatorname{falseScore}$; assume $\theta\le9E^8$ for $E=2^{2048(\operatorname{inputBits}(n)+1)}$, and the wanted-scan resource need fits at the layout header. The scan returns
--   $$
--   r\in\{0,1\},\qquad r=1\iff\theta<P(N)\ \lor\ \exists i<N,\ H_i.
--   $$
--   Its final counter equals $P(k)$, where $k=N$ on rejection and $k$ is the least accepted prefix length on success. The budget is $30+\sum_{i<N}(\operatorname{stepTime}(i)+300)$, with each step charged at its frozen prefix mass. Below the layout header only the counter cell may change.
--
--   This formalizes ascending physical-order scanning with immediate successful return.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedScanStored.lean#L23-L97

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
import Definitions.Def_ThreeSum1962Source_Bundle02
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
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_DenseGuardWanted_pair_indices_injective
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum_EncodedColorWantedConsumerData_incidence_length_le_magnitude
import Theorems.Thm_ThreeSum_EncodedColorWantedConsumerData_persistent_ends
import Theorems.Thm_ThreeSum_LightReportingWantedDispatchStored_program_meets
import Theorems.Thm_ThreeSum_LightReportingWantedScan_program_meets
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_Radix_representations_card_le
import Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_of_kept
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_output_count_le_magnitude
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le
import Theorems.Thm_ThreeSum_WantedRecordOrder_label_injective


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
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedPrefix
end ThreeSum.ReportingHostWantedPrefix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightReportingWantedScanStored.program_meets : ∀ {lim : Light.Limits} {μ : Nat → Int} {free n U d : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
  (hx :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U))
  (hp :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC))
  (hg :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)))
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hthreshold :
    @LE.le.{0} Nat instLENat (ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
  (hok :
    (ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim
      (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader d),
  Light.Meets lim ThreeSum.LightReportingWantedScan.program
    (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))) d
    (ThreeSum.LightReportingWantedDispatch.arguments (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
      (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC))
    μ
    (@ThreeSum.ReportingHostWantedConsumerData.scanTime μ free n color x A B C hsA hsB hsC
      (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (ThreeSum.LightReportingWantedScan.Accepted
            (@ThreeSum.ReportingHostWantedConsumerData.mass μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (@ThreeSum.ReportingHostWantedConsumerData.hit μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
            (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)))
        (And
          (ThreeSum.LightReportingWantedScan.Counter
            (@ThreeSum.ReportingHostWantedConsumerData.mass μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (@ThreeSum.ReportingHostWantedConsumerData.hit μ free n color x A B C hsA hsB hsC
              (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))
            (ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
            (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)
            (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter r ν)
          (Light.KeptBut μ ν (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
            (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  sorry
