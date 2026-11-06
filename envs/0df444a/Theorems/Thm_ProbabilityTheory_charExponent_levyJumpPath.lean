-- Prove2me | Theorems.Thm_ProbabilityTheory_charExponent_levyJumpPath
-- name    : ProbabilityTheory.charExponent_levyJumpPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:16:18.00628+00:00
-- url     : https://prove2.me/theorems/ec0e9f3b-0d78-44e5-8977-4697d8c0a52c
-- title:
--   LeanLevy: ProbabilityTheory.charExponent_levyJumpPath
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1769

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_isLevyProcess_levyJumpPath
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω}

theorem ProbabilityTheory.charExponent_levyJumpPath [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (ξ : ℝ) :
    (isLevyProcess_levyJumpPath hd hν b).charExponent ξ
      = (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ := by
  set ψ : ℂ := (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ with hψ
  simp only [IsLevyProcess.charExponent]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  have hcont : Filter.Tendsto (fun t : ℝ≥0 => (t : ℝ) * ψ.im) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 => (t : ℝ) * ψ.im) :=
      NNReal.continuous_coe.mul continuous_const
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    hcont.eventually (Metric.ball_mem_nhds (0 : ℝ) Real.pi_pos)] with t (ht : 0 < t) htim
  have hne : ((t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast NNReal.coe_ne_zero.mpr (ne_of_gt ht)
  have habs : |(t : ℝ) * ψ.im| < Real.pi := by simpa [Real.dist_eq] using htim
  obtain ⟨h1, h2⟩ := abs_lt.mp habs
  have him : (((t : ℝ) : ℂ) * ψ).im = (t : ℝ) * ψ.im := by simp [Complex.mul_im]
  have hlog : Complex.log (Complex.exp (((t : ℝ) : ℂ) * ψ)) = ((t : ℝ) : ℂ) * ψ :=
    Complex.log_exp (by rw [him]; exact h1) (by rw [him]; exact le_of_lt h2)
  rw [charFun_map_levyJumpPath hd hν b t ξ, hlog, eq_div_iff hne]; ring
