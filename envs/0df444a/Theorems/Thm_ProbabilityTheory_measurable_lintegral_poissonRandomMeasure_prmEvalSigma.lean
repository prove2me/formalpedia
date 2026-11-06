-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_lintegral_poissonRandomMeasure_prmEvalSigma
-- name    : ProbabilityTheory.measurable_lintegral_poissonRandomMeasure_prmEvalSigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:34:33.820031+00:00
-- url     : https://prove2.me/theorems/cefb07ae-2556-4731-9abc-d1262c36bf7b
-- title:
--   LeanLevy: ProbabilityTheory.measurable_lintegral_poissonRandomMeasure_prmEvalSigma
-- statement:
--   The Lebesgue integral of a region-supported function against the random measure is measurable Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonFiltration.lean#L101

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure

theorem ProbabilityTheory.measurable_lintegral_poissonRandomMeasure_prmEvalSigma : ∀ {Ω E : Type} [inst : MeasurableSpace E] {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → E}
  {m : @MeasureTheory.Measure E inst} {R : Set E},
  @MeasurableSet E inst R →
    @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
        (@DFunLike.coe (@MeasureTheory.Measure E inst) (Set E) (fun x => ENNReal)
          (@MeasureTheory.Measure.instFunLike E inst) m R)
        (@Top.top ENNReal ENNReal.instTop) →
      ∀ {g : E → ENNReal},
        @Measurable E ENNReal inst ENNReal.measurableSpace g →
          (∀ (x : E),
              Not (@Membership.mem E (Set E) (@Set.instMembership E) R x) →
                @Eq ENNReal (g x) (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero))) →
            @Measurable Ω ENNReal (@ProbabilityTheory.prmEvalSigma Ω E inst K X m R) ENNReal.measurableSpace fun ω =>
              @MeasureTheory.lintegral E inst (@ProbabilityTheory.poissonRandomMeasure Ω E inst K X ω) fun x => g x := by sorry
