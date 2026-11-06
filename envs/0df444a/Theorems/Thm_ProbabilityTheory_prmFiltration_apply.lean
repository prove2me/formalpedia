-- Prove2me | Theorems.Thm_ProbabilityTheory_prmFiltration_apply
-- name    : ProbabilityTheory.prmFiltration_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:06:31.752009+00:00
-- url     : https://prove2.me/theorems/4124e519-f1c7-45cf-aa51-af4920550456
-- title:
--   LeanLevy: ProbabilityTheory.prmFiltration_apply
-- statement:
--   Source theorem from LeanLevy. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonMartingale.lean#L96

import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson

theorem ProbabilityTheory.prmFiltration_apply : ∀ {E : Type} [inst : MeasurableSpace E] {m : @MeasureTheory.Measure E inst}
  [inst_1 : @MeasureTheory.SigmaFinite E inst m] {Ω : Type} [inst_2 : MeasurableSpace Ω] {K : Nat → Ω → Nat}
  {X : Nat → Nat → Ω → Prod Real E} {hK : ∀ (k : Nat), @Measurable Ω Nat inst_2 Nat.instMeasurableSpace (K k)}
  {hX :
    ∀ (k n : Nat),
      @Measurable Ω (Prod Real E) inst_2 (@Prod.instMeasurableSpace Real E Real.measurableSpace inst) (X k n)}
  (t : NNReal),
  @Eq (MeasurableSpace Ω)
    (@MeasureTheory.Filtration.seq Ω NNReal (@PartialOrder.toPreorder NNReal NNReal.instPartialOrder) inst_2
      (@ProbabilityTheory.prmFiltration E inst Ω inst_2 K X m inst_1 hK hX) t)
    (@ProbabilityTheory.prmEvalSigma Ω (Prod Real E)
      (@Prod.instMeasurableSpace Real E (@MeasureTheory.MeasureSpace.toMeasurableSpace Real Real.measureSpace) inst) K X
      (@MeasureTheory.Measure.prod Real E (@MeasureTheory.MeasureSpace.toMeasurableSpace Real Real.measureSpace) inst
        (@MeasureTheory.MeasureSpace.volume Real Real.measureSpace) m)
      (@SProd.sprod (Set Real) (Set E) (Set (Prod Real E)) (@Set.instSProd Real E) (@Set.Iic Real Real.instPreorder ↑t)
        (@Set.univ E))) := by sorry
