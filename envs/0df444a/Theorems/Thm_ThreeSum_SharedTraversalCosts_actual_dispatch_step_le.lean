-- Prove2me | Theorems.Thm_ThreeSum_SharedTraversalCosts_actual_dispatch_step_le
-- name    : ThreeSum.SharedTraversalCosts.actual_dispatch_step_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:21:14.23498+00:00
-- url     : https://prove2.me/theorems/56e2f6df-f0d4-4269-b805-86c433b7b4c1
-- title:
--   Charge one guarded wanted dispatch by its active root mass
-- statement:
--   Let finite domains $A,B,C$ carry integer values $a,b,c$, and let physical left/right arrays enumerate $B,C$ bijectively with matching values. Fix natural modulus $p$, shift $\sigma$, and a wanted key $w$ whose $A$ label lies in $A$ and whose lifted residue agrees with its global key modulo the global modulus. The dispatcher uses the scheduled dimensions, and every catalog cutoff through terminal depth equals the prescribed rounded switch. Let $m$ be the root mass of $w$ in the raw represented domain, $o$ the previous mass, and $\tau$ the guard threshold. With $H$ the scaled traversal overhead, $Q_0$ the initial query count, $G$ the micro-partition count, $Q$ all query counts, $T$ terminal choices, and $S_{4800}$ scalar overhead,
--   $$
--   \operatorname{dispatchTime}+300\le HQ_0+S_{4800}+
--   \begin{cases}0,&\tau<o+m,\\mH(GQ+T),&\tau\ge o+m.\end{cases}
--   $$
--   This keeps the costly search charge inside the actual cumulative guard.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SharedTraversalScanCosts.lean#L30-L70

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
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
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SharedTraversalCosts_expansion_le_layer
import Theorems.Thm_ThreeSum_SharedTraversalCosts_initial_le_layer
import Theorems.Thm_ThreeSum_SharedTraversalCosts_terminal_charge_le
import Theorems.Thm_ThreeSum_SharedTraversalCosts_wanted_time_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
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
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
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
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

universe u_1 u_2 u_3

theorem ThreeSum.SharedTraversalCosts.actual_dispatch_step_le : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {n NL NR old threshold : Nat}
  {cfg : ThreeSum.LightReportingWantedDispatch.Config} (hcH : @Eq.{1} Nat cfg.h (ThreeSum.SharedTraversalCosts.half n))
  (hcJ : @Eq.{1} Nat cfg.J (ThreeSum.SharedTraversalCosts.blocks n)) (p : Nat) (shift : Int) (A : Finset.{u_1} α)
  (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int) (left right : Nat → Int)
  (eL : Equiv.{1, u_2 + 1} (Fin NL) ↥B) (eR : Equiv.{1, u_3 + 1} (Fin NR) ↥C)
  (hvL :
    ∀ (i : Fin NL),
      @Eq.{1} Int (left (@Fin.val NL i))
        (b
          (@Subtype.val.{u_2 + 1} β
            (fun (x : β) =>
              @Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) B x)
            (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (fun (x : Fin NL) => ↥B)
              (@EquivLike.toFunLike.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (↥B)
                (@Equiv.instEquivLike.{1, u_2 + 1} (Fin NL) ↥B))
              eL i))))
  (hvR :
    ∀ (i : Fin NR),
      @Eq.{1} Int (right (@Fin.val NR i))
        (c
          (@Subtype.val.{u_3 + 1} γ
            (fun (x : γ) =>
              @Membership.mem.{u_3, u_3} γ (Finset.{u_3} γ)
                (@SetLike.instMembership.{u_3, u_3} (Finset.{u_3} γ) γ (@Finset.instSetLike.{u_3} γ)) C x)
            (@DFunLike.coe.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (fun (x : Fin NR) => ↥C)
              (@EquivLike.toFunLike.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (↥C)
                (@Equiv.instEquivLike.{1, u_3 + 1} (Fin NR) ↥C))
              eR i))))
  (w :
    ThreeSum.RawReporting.Wanted.{u_1} (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n)
      α)
  (D : Nat → ThreeSum.ReportingHostLevelData.Catalog) (hD : ThreeSum.SharedTraversalCosts.CatalogScales n D)
  (hkey :
    And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
        (@Prod.fst.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
              (ThreeSum.SharedTraversalCosts.blocks n)))
          w))
      (@Dvd.dvd.{0} Int Int.instDvd
        (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedTraversalCosts.half n)
          (ThreeSum.SharedTraversalCosts.blocks n))
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                (a
                  (@Prod.fst.{u_1, 0} α
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                        (ThreeSum.SharedTraversalCosts.blocks n)))
                    w))
                (@Nat.cast.{0} Int instNatCastInt p))
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (ThreeSum.RawIncidences.lift
                  (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                      (ThreeSum.SharedTraversalCosts.blocks n))
                    (@Prod.snd.{u_1, 0} α
                      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                          (ThreeSum.SharedTraversalCosts.blocks n)))
                      w)))
                (@Nat.cast.{0} Int instNatCastInt p)))
            shift)
          (@ThreeSum.GlobalEncoding.globalKey (ThreeSum.SharedTraversalCosts.half n)
            (ThreeSum.SharedTraversalCosts.blocks n)
            (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                (ThreeSum.SharedTraversalCosts.blocks n))
              (@Prod.snd.{u_1, 0} α
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                    (ThreeSum.SharedTraversalCosts.blocks n)))
                w)))))),
  have I :=
    @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ (ThreeSum.SharedTraversalCosts.half n)
      (ThreeSum.SharedTraversalCosts.blocks n) (@Nat.cast.{0} Int instNatCastInt p) shift
      (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
        (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
        (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
        (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
        (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
      a b c;
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (ThreeSum.LightReportingWantedDispatch.time cfg (ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
        (@ThreeSum.LightReportingWanted.time.{u_1, u_2, u_3} α β γ inst (ThreeSum.SharedTraversalCosts.half n)
          (ThreeSum.SharedTraversalCosts.blocks n) p shift left right NL NR old threshold I w D
          (ThreeSum.Switch.terminalDepth n)))
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
            (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst
              (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n) I w)))
        (threshold.decLt
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
            (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst
              (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n) I w)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst
            (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n) I w)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (ThreeSum.SharedTraversalCosts.scaledOverhead n)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.CostLedger.microPartitions n)
                (ThreeSum.CostLedger.allQueryTerms n))
              (ThreeSum.StageBounds.terminalChoices n)))))) := by
  sorry
