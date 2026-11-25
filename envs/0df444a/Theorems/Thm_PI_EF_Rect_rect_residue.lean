-- Prove2me | Theorems.Thm_PI_EF_Rect_rect_residue
-- name    : PI.EF.Rect.rect_residue
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:42.410624+00:00
-- url     : https://prove2.me/theorems/6a6cc363-7b70-533e-9627-24399704c8ae
-- title:
--   Rect: rect residue
-- statement:
--   The Rect construction uses the rect residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L389-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L389-L402

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

theorem PI.EF.Rect.rect_residue {z w : ℂ} {H : ℂ → ℂ} (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ) {u : ℝ} (hu : 0 < u)
    (h0 : (0 : ℂ) ∈ rectOpen z w) (hH : DifferentiableOn ℂ H (rectClosed z w))
    (hZ : ∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ ∈ rectOpen z w) :
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * ((u : ℂ) ^ s / s)) z w =
      2 * π * I * (H 0 + (∑ ρ ∈ Z, wt ρ * (((u : ℂ) ^ ρ - 1) / ρ)) + e * Real.log u) := by sorry
