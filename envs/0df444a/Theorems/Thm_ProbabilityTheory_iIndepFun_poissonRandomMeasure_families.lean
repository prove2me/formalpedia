-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_families
-- name    : ProbabilityTheory.iIndepFun_poissonRandomMeasure_families
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:28:34.236732+00:00
-- url     : https://prove2.me/theorems/ffd74632-4b3b-4359-b51b-48eaea4853a2
-- title:
--   LeanLevy: ProbabilityTheory.iIndepFun_poissonRandomMeasure_families
-- statement:
--   Mutual cross-family independence: finitely many finite families of finite-mass evaluation Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonFiltration.lean#L284

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure

theorem ProbabilityTheory.iIndepFun_poissonRandomMeasure_families : ∀ {Ω E : Type} [inst : MeasurableSpace Ω] [inst_1 : MeasurableSpace E] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst_1} {μ : @MeasureTheory.Measure Ω inst}
  [inst_2 : @MeasureTheory.SigmaFinite E inst_1 m] [inst_3 : Nonempty E] [@MeasureTheory.IsProbabilityMeasure Ω inst μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst_1 inst K X m inst_2 inst_3 μ →
    ∀ {ι : Type} [Fintype ι] {ιB : ι → Type} [(i : ι) → Fintype (ιB i)] {B : (i : ι) → ιB i → Set E},
      (∀ (i : ι) (b : ιB i), @MeasurableSet E inst_1 (B i b)) →
        (∀ (i : ι) (b : ιB i),
            @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
              (@DFunLike.coe (@MeasureTheory.Measure E inst_1) (Set E) (fun x => ENNReal)
                (@MeasureTheory.Measure.instFunLike E inst_1) m (B i b))
              (@Top.top ENNReal ENNReal.instTop)) →
          (∀ (i j : ι),
              @Ne ι i j →
                ∀ (b : ιB i) (b' : ιB j),
                  @Disjoint (Set E)
                    (@ChainCompletePartialOrder.toPartialOrder (Set E)
                      (@ChainCompletePartialOrder.instOfCompleteLattice (Set E)
                        (@CompleteBooleanAlgebra.toCompleteLattice (Set E)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set E)
                            (@Set.instCompleteAtomicBooleanAlgebra E)))))
                    (@HeytingAlgebra.toOrderBot (Set E)
                      (@Order.Frame.toHeytingAlgebra (Set E)
                        (@CompleteDistribLattice.toFrame (Set E)
                          (@CompleteBooleanAlgebra.toCompleteDistribLattice (Set E)
                            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set E)
                              (@Set.instCompleteAtomicBooleanAlgebra E))))))
                    (B i b) (B j b')) →
            @ProbabilityTheory.iIndepFun Ω ι inst (fun i => ιB i → ENNReal)
              (fun x => @MeasurableSpace.pi (ιB x) (fun b => ENNReal) fun a => ENNReal.measurableSpace)
              (fun i ω b =>
                @DFunLike.coe (@MeasureTheory.Measure E inst_1) (Set E) (fun x => ENNReal)
                  (@MeasureTheory.Measure.instFunLike E inst_1)
                  (@ProbabilityTheory.poissonRandomMeasure Ω E inst_1 K X ω) (B i b))
              μ := by sorry
