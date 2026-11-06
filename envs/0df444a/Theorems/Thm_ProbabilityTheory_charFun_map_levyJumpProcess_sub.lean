-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpProcess_sub
-- name    : ProbabilityTheory.charFun_map_levyJumpProcess_sub
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:37:16.416336+00:00
-- url     : https://prove2.me/theorems/b1ae50a0-651a-4f4b-8b66-1564fa5f5882
-- title:
--   LeanLevy: ProbabilityTheory.charFun_map_levyJumpProcess_sub
-- statement:
--   **The increment law of the jump process:** `exp ((t−s) · ψ_{(b,0,ν)})`. The two banded jump The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpLaw.lean#L224

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

theorem ProbabilityTheory.charFun_map_levyJumpProcess_sub
    {Ω : Type} [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
    {ν : MeasureTheory.Measure ℝ} [MeasureTheory.SigmaFinite ν]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (hd : ProbabilityTheory.IsPoissonPointFamily K X (MeasureTheory.volume.prod ν) μ)
    (hν : ProbabilityTheory.IsLevyMeasure ν) (b : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (ξ : ℝ) :
    MeasureTheory.charFun
        (MeasureTheory.Measure.map
          (fun ω => ProbabilityTheory.levyJumpProcess hd hν b t ω -
            ProbabilityTheory.levyJumpProcess hd hν b s ω) μ)
        ξ =
      Complex.exp
        ((((t : ℝ) - (s : ℝ) : ℝ) : ℂ) *
          (ProbabilityTheory.LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by sorry
