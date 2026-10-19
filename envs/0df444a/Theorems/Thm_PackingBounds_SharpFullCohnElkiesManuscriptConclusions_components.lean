-- Prove2me | Theorems.Thm_PackingBounds_SharpFullCohnElkiesManuscriptConclusions_components
-- name    : PackingBounds.SharpFullCohnElkiesManuscriptConclusions.components
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:05.603159+00:00
-- url     : https://prove2.me/theorems/6861fc60-6c55-46d4-98ec-18876ac16ba7
-- title:
--   PackingBounds.SharpFullCohnElkiesManuscriptConclusions.components
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
open PackingBounds

theorem PackingBounds.SharpFullCohnElkiesManuscriptConclusions.components :
    Tendsto
        (fun d : ℕ =>
          sInf {q : ℝ | ∃ f : FullAdmissible d,
            fullQuotient f ^ ((d : ℝ)⁻¹) = q} /
            Real.sqrt (d : ℝ))
        atTop (𝓝 (1 / Real.pi)) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        ∀ d : ℕ, 0 < d →
          sInf {q : ℝ | ∃ f : FullAdmissible d,
            fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
            (1 / Real.pi + err d) * Real.sqrt (d : ℝ)) ∧
      Tendsto
        (fun d : ℕ => (fullLinearProgram d) ^ ((d : ℝ)⁻¹))
        atTop (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi)))) ∧
      Tendsto
        (fun d : ℕ => Real.log (fullLinearProgram d) / (d : ℝ))
        atTop
        (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi)))) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        (∀ᶠ d : ℕ in atTop,
          fullLinearProgram d =
            (Real.sqrt (Real.exp 1 / (2 * Real.pi)) + err d) ^ d)) ∧
      (∃ δ : ℕ → ℝ,
        Tendsto δ atTop (𝓝 0) ∧
        (∀ d : ℕ, 0 ≤ δ d) ∧
        (∀ᶠ d : ℕ in atTop, ∀ f : FullAdmissible d,
          (2 : ℝ) ^ d / CohnElkies.unitBallVolume d *
            (Real.sqrt (Real.exp 1 / (2 * Real.pi)) - δ d) ^ d ≤
              fullQuotient f)) ∧
      0 < (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∧
      (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∈
        Set.Ioo
          (0.604400544291677695341677307053 : ℝ)
          0.604400544291677695341677307054 ∧
      Tendsto
        (fun d : ℕ => Real.logb 2 (fullLinearProgram d) / (d : ℝ))
        atTop
        (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)))) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        (∀ᶠ d : ℕ in atTop,
          fullLinearProgram d =
            (2 : ℝ) ^
              (-((1 / 2 : ℝ) *
                  Real.logb 2 (2 * Real.pi / Real.exp 1) + err d) *
                (d : ℝ)))) := by sorry
