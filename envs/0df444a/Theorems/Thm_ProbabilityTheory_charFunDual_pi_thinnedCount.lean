-- Prove2me | Theorems.Thm_ProbabilityTheory_charFunDual_pi_thinnedCount
-- name    : ProbabilityTheory.charFunDual_pi_thinnedCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:27:59.852772+00:00
-- url     : https://prove2.me/theorems/eeee44dd-7b11-45a5-bab4-09f6845338c3
-- title:
--   LeanLevy: ProbabilityTheory.charFunDual_pi_thinnedCount
-- statement:
--   The joint characteristic function (via the dual of `ι → ℝ`) of the pushforward of a finite family Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L1394

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

theorem ProbabilityTheory.charFunDual_pi_thinnedCount : ∀ {Ω E : Type} [inst : MeasurableSpace E] [inst_1 : MeasurableSpace Ω] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst} [inst_2 : @MeasureTheory.SigmaFinite E inst m] [inst_3 : Nonempty E]
  {μ : @MeasureTheory.Measure Ω inst_1} {k : Nat} {ι : Type} [inst_4 : Fintype ι] [inst_5 : DecidableEq ι]
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
          ∀
            (L :
              @StrongDual Real Real.semiring
                (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                (ι → Real)
                (@Pi.topologicalSpace ι (fun a => Real) fun i =>
                  @UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                (@Pi.addCommMonoid ι (fun a => Real) fun i => Real.instAddCommMonoid)
                (@Pi.Function.module ι Real Real Real.semiring Real.instAddCommMonoid
                  (@Semiring.toModule Real Real.semiring))),
            @Eq Complex
              (@MeasureTheory.charFunDual (ι → Real)
                (@Pi.normedAddCommGroup ι (fun i => Real) inst_4 fun i => Real.normedAddCommGroup)
                (@Pi.normedSpace Real Real.normedField ι (fun i => Real) inst_4
                  (fun i =>
                    @NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
                          (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))
                  fun i =>
                  @InnerProductSpace.toNormedSpace Real Real Real.instRCLike
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
                          (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))
                    (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
                (@MeasurableSpace.pi ι (fun i => Real) fun a => Real.measurableSpace)
                (@MeasureTheory.Measure.map Ω (ι → Real) inst_1
                  (@MeasurableSpace.pi ι (fun i => Real) fun a => Real.measurableSpace)
                  (fun ω i => @Nat.cast Real Real.instNatCast (@ProbabilityTheory.thinnedCount Ω E K X (A i) k ω)) μ)
                L)
              (@Finset.prod ι Complex (@CommRing.toCommMonoid Complex Complex.commRing) (@Finset.univ ι inst_4) fun i =>
                Complex.exp
                  (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                    (↑(@DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
                          (@MeasureTheory.Measure.instFunLike E inst) m
                          (@Inter.inter (Set E) (@Set.instInter E) (@ProbabilityTheory.prmPiece E inst m inst_2 k)
                            (A i))).toReal)
                    (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub)
                      (Complex.exp
                        (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                          (↑(@DFunLike.coe
                              (@StrongDual Real Real.semiring
                                (@UniformSpace.toTopologicalSpace Real
                                  (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                (ι → Real)
                                (@Pi.topologicalSpace ι (fun a => Real) fun i =>
                                  @UniformSpace.toTopologicalSpace Real
                                    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid ι (fun a => Real) fun i => Real.instAddCommMonoid)
                                (@Pi.Function.module ι Real Real Real.semiring Real.instAddCommMonoid
                                  (@Semiring.toModule Real Real.semiring)))
                              (ι → Real) (fun x => Real)
                              (@ContinuousLinearMap.funLike Real Real Real.semiring Real.semiring
                                (@RingHom.id Real (@Semiring.toNonAssocSemiring Real Real.semiring)) (ι → Real)
                                (@Pi.topologicalSpace ι (fun a => Real) fun i =>
                                  @UniformSpace.toTopologicalSpace Real
                                    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                (@Pi.addCommMonoid ι (fun a => Real) fun i => Real.instAddCommMonoid) Real
                                (@UniformSpace.toTopologicalSpace Real
                                  (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
                                (@Semiring.toAddCommMonoid Real Real.semiring)
                                (@Pi.Function.module ι Real Real Real.semiring Real.instAddCommMonoid
                                  (@Semiring.toModule Real Real.semiring))
                                (@Semiring.toModule Real Real.semiring))
                              L
                              (@Pi.single ι (fun a => Real) (fun i => Real.instZero) inst_5 i
                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))))
                          Complex.I))
                      (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))))) := by sorry
