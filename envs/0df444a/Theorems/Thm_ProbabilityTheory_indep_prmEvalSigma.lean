-- Prove2me | Theorems.Thm_ProbabilityTheory_indep_prmEvalSigma
-- name    : ProbabilityTheory.indep_prmEvalSigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:30:27.897781+00:00
-- url     : https://prove2.me/theorems/4a6e0f27-aea6-4c24-b561-56a449f467bf
-- title:
--   LeanLevy: ProbabilityTheory.indep_prmEvalSigma
-- statement:
--   **The Poisson random measure is independently scattered at the sigma-algebra level:** the Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonFiltration.lean#L421

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure

theorem ProbabilityTheory.indep_prmEvalSigma : ∀ {Ω E : Type} [inst : MeasurableSpace Ω] [inst_1 : MeasurableSpace E] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst_1} {μ : @MeasureTheory.Measure Ω inst}
  [inst_2 : @MeasureTheory.SigmaFinite E inst_1 m] [inst_3 : Nonempty E] [@MeasureTheory.IsProbabilityMeasure Ω inst μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst_1 inst K X m inst_2 inst_3 μ →
    ∀ {R S : Set E},
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
          R S →
        @ProbabilityTheory.Indep Ω (@ProbabilityTheory.prmEvalSigma Ω E inst_1 K X m R)
          (@ProbabilityTheory.prmEvalSigma Ω E inst_1 K X m S) inst μ := by sorry
