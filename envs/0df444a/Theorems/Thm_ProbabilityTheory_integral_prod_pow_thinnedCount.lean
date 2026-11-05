-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_prod_pow_thinnedCount
-- name    : ProbabilityTheory.integral_prod_pow_thinnedCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:31:59.276992+00:00
-- url     : https://prove2.me/theorems/c7a8b3b0-121e-44f8-87fe-f48a609cabbd
-- title:
--   LeanLevy: ProbabilityTheory.integral_prod_pow_thinnedCount
-- statement:
--   **Joint pgf identity within a piece.** For a pairwise disjoint family of measurable sets, the Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L1341

import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_LeanLevy_Probability_Poisson

theorem ProbabilityTheory.integral_prod_pow_thinnedCount : ∀ {Ω E : Type} [inst : MeasurableSpace E] [inst_1 : MeasurableSpace Ω] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst} [inst_2 : @MeasureTheory.SigmaFinite E inst m] [inst_3 : Nonempty E]
  {μ : @MeasureTheory.Measure Ω inst_1} {k : Nat} {ι : Type} [inst_4 : Fintype ι]
  [@MeasureTheory.IsProbabilityMeasure Ω inst_1 μ],
  @ProbabilityTheory.IsPoissonPointFamily Ω E inst inst_1 K X m inst_2 inst_3 μ →
    ∀ {A : ι → Set E},
      (∀ (i : ι), @MeasurableSet E inst (A i)) →
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
              A) →
          ∀ (z : ι → Complex),
            (∀ (i : ι),
                @LE.le Real Real.instLE (@Norm.norm Complex Complex.instNorm (z i))
                  (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
              @Eq Complex
                (@MeasureTheory.integral Ω Complex Complex.instNormedAddCommGroup
                  (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                    instInnerProductSpaceRealComplex)
                  inst_1 μ fun ω =>
                  @Finset.prod ι Complex (@CommRing.toCommMonoid Complex Complex.commRing) (@Finset.univ ι inst_4)
                    fun i =>
                    @HPow.hPow Complex Nat Complex
                      (@instHPow Complex Nat
                        (@NPow.toPow Complex
                          (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))
                      (z i) (@ProbabilityTheory.thinnedCount Ω E K X (A i) k ω))
                (@Finset.prod ι Complex (@CommRing.toCommMonoid Complex Complex.commRing) (@Finset.univ ι inst_4)
                  fun i =>
                  Complex.exp
                    (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                      (↑(@DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
                            (@MeasureTheory.Measure.instFunLike E inst) m
                            (@Inter.inter (Set E) (@Set.instInter E) (@ProbabilityTheory.prmPiece E inst m inst_2 k)
                              (A i))).toReal)
                      (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) (z i)
                        (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))))) := by sorry
