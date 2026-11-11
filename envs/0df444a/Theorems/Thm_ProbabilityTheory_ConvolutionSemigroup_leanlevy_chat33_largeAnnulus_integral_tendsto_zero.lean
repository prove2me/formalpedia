-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_largeAnnulus_integral_tendsto_zero
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeAnnulus_integral_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:45:03.303221+00:00
-- url     : https://prove2.me/theorems/ba938d3c-beff-44fd-bb03-7a8802eb664e
-- title:
--   Annulus cutoff integral tends to zero under no boundary atom
-- statement:
--   For a Lévy measure with zero atom at |x|=rho, shifted smooth annulus BCFs have integrals tending to zero, dominated by the finite tail |x|≥rho/3.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3494-L3543

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeAnnulus_integral_tendsto_zero (ρ : ℝ) (hρ : 0 < ρ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_atom : ν {x | |x| = ρ} = 0) :
    ∃ f : ℕ → BoundedContinuousFunction ℝ ℝ,
      (∀ n x, f n x = max 0 (1 - ((n + 2 : ℝ) / ρ) *
        max 0 (|(|x| - ρ)| - ρ / (n + 2 : ℝ)))) ∧
      Tendsto (fun n => ∫ x, f n x ∂ν) atTop (𝓝 0) := by sorry
