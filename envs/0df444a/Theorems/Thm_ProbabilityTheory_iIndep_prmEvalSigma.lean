-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndep_prmEvalSigma
-- name    : ProbabilityTheory.iIndep_prmEvalSigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:29:21.399363+00:00
-- url     : https://prove2.me/theorems/876ce088-8bc0-4e45-9974-5ea7533ac623
-- title:
--   LeanLevy: ProbabilityTheory.iIndep_prmEvalSigma
-- statement:
--   **The Poisson random measure is mutually independently scattered:** the evaluation Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonFiltration.lean#L340

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure

theorem ProbabilityTheory.iIndep_prmEvalSigma : ∀ {Ω E : Type} [inst : MeasurableSpace Ω] [inst_1 : MeasurableSpace E] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst_1} {μ : @MeasureTheory.Measure Ω inst}
  [inst_2 : @MeasureTheory.SigmaFinite E inst_1 m] [inst_3 : Nonempty E] [@MeasureTheory.IsProbabilityMeasure Ω inst μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst_1 inst K X m inst_2 inst_3 μ →
    ∀ {ι : Type} [Fintype ι] {R : ι → Set E},
      @Pairwise ι
          (@Function.onFun ι (Set E) Prop
            (@Disjoint (Set E)
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
                        (@Set.instCompleteAtomicBooleanAlgebra E)))))))
            R) →
        @ProbabilityTheory.iIndep Ω ι (fun i => @ProbabilityTheory.prmEvalSigma Ω E inst_1 K X m (R i)) inst μ := by sorry
