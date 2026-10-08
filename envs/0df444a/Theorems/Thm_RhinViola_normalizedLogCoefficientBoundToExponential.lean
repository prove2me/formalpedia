-- Prove2me | Theorems.Thm_RhinViola_normalizedLogCoefficientBoundToExponential
-- name    : RhinViola.normalizedLogCoefficientBoundToExponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:43:43.350474+00:00
-- url     : https://prove2.me/theorems/ade44fed-58e7-43a5-ac00-a68eb120bef7
-- title:
--   Convert a normalized logarithmic coefficient bound to exponential growth
-- statement:
--   For a positive natural n, the normalized logarithmic upper bound log|b|/n≤ρ+δ implies the exponential coefficient bound |b|≤exp((ρ+δ)n). The zero coefficient case is immediate; otherwise exponentiate the logarithmic inequality.
-- source:
--   Elementary logarithm/exponential conversion used in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem RhinViola.normalizedLogCoefficientBoundToExponential
    (ρ δ : ℝ) (b : ℤ) (n : ℕ)
    (hn : 0 < n)
    (hlog : Real.log |(b : ℝ)| / (n : ℝ) ≤ ρ + δ) :
    |(b : ℝ)| ≤ Real.exp ((ρ + δ) * (n : ℝ)) := by sorry
