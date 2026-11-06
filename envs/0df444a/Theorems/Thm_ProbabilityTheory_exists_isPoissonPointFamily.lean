-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
-- name    : ProbabilityTheory.exists_isPoissonPointFamily
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:53:54.895371+00:00
-- url     : https://prove2.me/theorems/046cc13e-7089-4dde-943a-d511d648f5ce
-- title:
--   LeanLevy: ProbabilityTheory.exists_isPoissonPointFamily
-- statement:
--   **Existence of the Poisson point family.** For any σ-finite intensity `m` on `E` there is a Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L254

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

theorem ProbabilityTheory.exists_isPoissonPointFamily : ∀ {E : Type} [inst : MeasurableSpace E] (m : @MeasureTheory.Measure E inst)
  [inst_1 : @MeasureTheory.SigmaFinite E inst m] [inst_2 : Nonempty E],
  @Exists Type fun Ω =>
    @Exists (MeasurableSpace Ω) fun x =>
      @Exists (@MeasureTheory.Measure Ω x) fun μ =>
        @Exists (Nat → Ω → Nat) fun K =>
          @Exists (Nat → Nat → Ω → E) fun X =>
            And (@MeasureTheory.IsProbabilityMeasure Ω x μ)
              (@ProbabilityTheory.IsPoissonPointFamily Ω E inst x K X m inst_1 inst_2 μ) := by sorry
