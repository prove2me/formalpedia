-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumWantedHostCosts_physical_step_le
-- name    : ThreeSum.ThreeSumWantedHostCosts.physical_step_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:32:57.465322+00:00
-- url     : https://prove2.me/theorems/12b155ec-d717-4050-a3e9-188786d2c98c
-- title:
--   Per-wanted-record cost with the dense-threshold branch
-- statement:
--   Let $A,B,C$ be strictly increasing integer lists, and let $w$ be a physical wanted label for the input schedule at size $n$. Its A incidence, lift, and global output satisfy the selected-prime global-key congruence. Let $m_w$ be the exact raw-incidence mass of this label, $o$ the previous accumulated mass, and $\tau$ the threshold. Define $G(n)$ as the scaled traversal overhead and $S(n)$ as the scalar dispatch allowance with parameter $4800$.
--
--   For the actual retained host configuration at any free address and output index, the dispatch budget plus its $300$-step allowance is at most
--   $$G(n)Q_{n,0}+S(n)+\begin{cases}0,&\tau<o+m_w,\\m_wG(n)\bigl(P_n\sum_{j\le K_n}Q_{n,j}+2^{r_{n,K_n}}\bigr),&\tau\ge o+m_w,\end{cases}$$
--   where $Q_{n,j}$ are query counts, $P_n$ the microblock partition count, $K_n$ the terminal depth, and $r_{n,K_n}$ the terminal residual size.
--
--   The bound accounts for the executed threshold decision before charging mass-proportional traversal.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ThreeSumWantedHostCosts.lean#L14-L51

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_SharedTraversalCosts_actual_dispatch_step_le


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
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

theorem ThreeSum.ThreeSumWantedHostCosts.physical_step_le : ∀ {free n output old threshold : Nat} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (w : ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC)
  (hkey :
    @Dvd.dvd.{0} Int Int.instDvd
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedTraversalCosts.half n)
        (ThreeSum.SharedTraversalCosts.blocks n))
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
                (fun (j : Nat) => @List.getD.{0} Int A j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                (@Fin.val
                  (@List.length.{0} ThreeSum.BandRawA.Label
                    (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)))
                  (@Prod.fst.{0, 0}
                    (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A)
                      (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (ThreeSum.RawIncidences.lift
                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n))
                  (@Prod.snd.{0, 0}
                    (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A)
                      (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC))))
          (ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC))
        (@ThreeSum.GlobalEncoding.globalKey (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n)
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            (@Prod.snd.{0, 0}
              (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))))),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (ThreeSum.LightReportingWantedDispatch.time (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
        (ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
        (ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC w output old threshold))
      (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (ThreeSum.SharedTraversalCosts.scaledOverhead n)
          (ThreeSum.CostLedger.queryTerms n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (ThreeSum.SharedTraversalCosts.scalarOverhead
          (@OfNat.ofNat.{0} Nat (nat_lit 4800) (instOfNatNat (nat_lit 4800))) n))
      (@ite.{1} Nat
        (@LT.lt.{0} Nat instLTNat threshold
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
            (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)))
        (threshold.decLt
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
            (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (ThreeSum.SharedTraversalCosts.scaledOverhead n)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.CostLedger.microPartitions n)
                (ThreeSum.CostLedger.allQueryTerms n))
              (ThreeSum.StageBounds.terminalChoices n)))))) := by
  sorry
