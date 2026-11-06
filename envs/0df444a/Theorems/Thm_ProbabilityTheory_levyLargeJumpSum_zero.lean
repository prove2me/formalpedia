-- Prove2me | Theorems.Thm_ProbabilityTheory_levyLargeJumpSum_zero
-- name    : ProbabilityTheory.levyLargeJumpSum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:05:58.791435+00:00
-- url     : https://prove2.me/theorems/24a555a5-7b39-462f-a5a8-457214a16a91
-- title:
--   LeanLevy: ProbabilityTheory.levyLargeJumpSum_zero
-- statement:
--   The large-jump sum vanishes at time zero: the band `(0, 0] × {x | 1 ≤ |x|}` is empty. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L440

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

theorem ProbabilityTheory.levyLargeJumpSum_zero : ∀ {Ω : Type} {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → Prod Real Real} (ω : Ω),
  @Eq Real
    (@ProbabilityTheory.levyLargeJumpSum Ω K X (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ω)
    (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) := by sorry
