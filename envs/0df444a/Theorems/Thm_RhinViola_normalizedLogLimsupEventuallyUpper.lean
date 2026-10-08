-- Prove2me | Theorems.Thm_RhinViola_normalizedLogLimsupEventuallyUpper
-- name    : RhinViola.normalizedLogLimsupEventuallyUpper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T17:13:59.544086+00:00
-- url     : https://prove2.me/theorems/516a158d-f67a-4dca-83ab-4bc534c05ba1
-- title:
--   A normalized logarithmic limsup gives an eventual upper band
-- statement:
--   If a real sequence g_n is eventually bounded above in the filter sense and limsup g_n≤ρ, then for every δ>0 it eventually satisfies g_n≤ρ+δ. This is the coefficient-growth wrapper needed in Rhin–Viola Lemma 4.
-- source:
--   Elementary consequence of the limsup hypothesis in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

theorem RhinViola.normalizedLogLimsupEventuallyUpper
    (ρ δ : ℝ) (g : ℕ → ℝ)
    (hδ : 0 < δ)
    (hbounded : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop g)
    (hlimsup : Filter.limsup g Filter.atTop ≤ ρ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → g n ≤ ρ + δ := by sorry
