-- Prove2me | Theorems.Thm_ProbabilityTheory_eLpNorm_smallJumpBand_sub_bandFun_aux
-- name    : ProbabilityTheory.eLpNorm_smallJumpBand_sub_bandFun_aux
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:10:16.91819+00:00
-- url     : https://prove2.me/theorems/1fd4de94-3216-4cad-bd51-fe98dbc29d3e
-- title:
--   LeanLevy auxiliary: small-jump band truncation L2 norm identity
-- statement:
--   Source-exact L2 isometry identity for the difference of a compensated small-jump integral and finite-mass band truncation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L1345

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem ProbabilityTheory.eLpNorm_smallJumpBand_sub_bandFun_aux [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (s t : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Set.Ioo (-1) 1) (hBfin : ν B < ⊤) :
    eLpNorm (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hB hBsub hBfin s t).toLp
            ((Set.Ioc s t ×ˢ B).indicator fun p => p.2))) 2 μ
      = eLpNorm ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)).indicator fun p : ℝ × ℝ => p.2) 2
          (volume.prod ν) := by sorry
