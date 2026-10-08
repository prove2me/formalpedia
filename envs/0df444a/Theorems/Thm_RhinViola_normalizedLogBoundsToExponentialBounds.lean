-- Prove2me | Theorems.Thm_RhinViola_normalizedLogBoundsToExponentialBounds
-- name    : RhinViola.normalizedLogBoundsToExponentialBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:41:21.049576+00:00
-- url     : https://prove2.me/theorems/d5225205-1ca8-490b-8cd7-7e03b874cf86
-- title:
--   Convert normalized logarithmic linear-form bounds to exponential bounds
-- statement:
--   For a nonzero real linear form f and positive natural n, a normalized logarithmic band -(σ+δ)≤log|f|/n≤-(σ-δ) is equivalent in the needed direction to the exponential envelope exp(-(σ+δ)n)≤|f|≤exp(-(σ-δ)n).
-- source:
--   Elementary logarithm/exponential conversion used in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem RhinViola.normalizedLogBoundsToExponentialBounds
    (σ δ f : ℝ) (n : ℕ)
    (hn : 0 < n) (hf : f ≠ 0)
    (hlo : -(σ + δ) ≤ Real.log |f| / (n : ℝ))
    (hhi : Real.log |f| / (n : ℝ) ≤ -(σ - δ)) :
    Real.exp (-((σ + δ) * (n : ℝ))) ≤ |f| ∧
      |f| ≤ Real.exp (-((σ - δ) * (n : ℝ))) := by sorry
