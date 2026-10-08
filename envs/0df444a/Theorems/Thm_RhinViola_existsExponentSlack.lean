-- Prove2me | Theorems.Thm_RhinViola_existsExponentSlack
-- name    : RhinViola.existsExponentSlack
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T07:56:13.984203+00:00
-- url     : https://prove2.me/theorems/59bd9dd9-1bf2-4400-bb54-f79583704405
-- title:
--   Explicit exponent slack for the Rhin–Viola irrationality criterion
-- statement:
--   For positive decay rate σ, nonnegative coefficient-growth rate ρ and any ε>0, there is an explicit slack 0<δ<σ such that the perturbed Rhin–Viola exponent (σ+ρ+2δ)/(σ−δ) is strictly below 1+ρ/σ+ε. This is the epsilon-budget step in the abstract irrationality-measure criterion.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Tactic

theorem RhinViola.existsExponentSlack
    (σ ρ ε : ℝ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < σ ∧
      (σ + ρ + 2 * δ) / (σ - δ) < 1 + ρ / σ + ε := by sorry
