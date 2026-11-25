-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenGainPolynomial_fc_poly
-- name    : PositivityTheory.CW.EigenGainPolynomial.fc_poly
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:23.752212+00:00
-- url     : https://prove2.me/theorems/d9624299-ed0c-48b8-bb3f-351e5c44f150
-- title:
--   Eigen Gain Polynomial: fc poly
-- statement:
--   The Eigen Gain Polynomial construction uses the fc poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisFormSumOfGain.lean#L34-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisFormSumOfGain.lean#L34-L71

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisFormSumOfGain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenGainPolynomial

theorem PositivityTheory.CW.EigenGainPolynomial.fc_poly {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (ν k0 k1 k2 k4 : ℝ) (w : V) :
    (inner ℂ w (fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) w)).re =
      k0 * ‖w‖ ^ 2 + k1 * (inner ℂ w (fc b μ (fun x => x - ν) w)).re
        + k2 * ‖fc b μ (fun x => x - ν) w‖ ^ 2
        + k4 * ‖fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) w)‖ ^ 2 := by sorry
