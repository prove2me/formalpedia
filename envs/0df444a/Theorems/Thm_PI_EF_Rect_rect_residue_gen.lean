-- Prove2me | Theorems.Thm_PI_EF_Rect_rect_residue_gen
-- name    : PI.EF.Rect.rect_residue_gen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:48.534916+00:00
-- url     : https://prove2.me/theorems/50a64ac4-c80a-54de-859f-031924e0bed1
-- title:
--   Rect: rect residue gen
-- statement:
--   The Rect construction uses the rect residue gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L333-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L333-L387

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real

theorem PI.EF.Rect.rect_residue_gen {z w : ℂ} {H E : ℂ → ℂ} (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ)
    (h0 : (0 : ℂ) ∈ rectOpen z w) (hH : DifferentiableOn ℂ H (rectClosed z w))
    (hE : DifferentiableOn ℂ E (rectClosed z w)) (hZ : ∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ ∈ rectOpen z w) :
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * (E s / s)) z w =
      2 * π * I * (H 0 * E 0 + (∑ ρ ∈ Z, wt ρ * ((E ρ - E 0) / ρ)) + e * deriv E 0) := by sorry
