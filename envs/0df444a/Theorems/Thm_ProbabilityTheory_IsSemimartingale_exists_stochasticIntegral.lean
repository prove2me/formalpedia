-- Prove2me | Theorems.Thm_ProbabilityTheory_IsSemimartingale_exists_stochasticIntegral
-- name    : ProbabilityTheory.IsSemimartingale.exists_stochasticIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:58:16.273319+00:00
-- url     : https://prove2.me/theorems/997e74af-726a-46c9-8ac4-25c16d266734
-- title:
--   Existence of the stochastic integral for a semimartingale
-- statement:
--   For a real semimartingale X on a filtered finite-measure space satisfying the usual conditions, and an adapted integrand H with almost surely caglad paths, there exists an adapted process J with cadlag paths such that every simple predictable approximation to H in uniform convergence on compact time intervals in probability has elementary integrals converging in the same sense to J. This is the original StochLean construction theorem.
-- source:
--   StochLean.Probability.Process.Semimartingale.StochasticIntegral.Construction

import Definitions.Def_SourceProof_361655cd6ef42aa35eef5e59

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem ProbabilityTheory.IsSemimartingale.exists_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      ∀ S : ℕ → ℝ≥0 → Ω → ℝ, ∀ hS : ∀ n, IsSimplePredictable (S n) F,
        TendstoUCP P S atTop H →
          TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J := by sorry
