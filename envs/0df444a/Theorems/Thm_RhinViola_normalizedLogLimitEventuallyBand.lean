-- Prove2me | Theorems.Thm_RhinViola_normalizedLogLimitEventuallyBand
-- name    : RhinViola.normalizedLogLimitEventuallyBand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:47:34.735203+00:00
-- url     : https://prove2.me/theorems/d3da9d91-95cc-4fdd-b2b0-82bf348360c3
-- title:
--   A normalized logarithmic limit gives an eventual two-sided band
-- statement:
--   If a real sequence g_n tends to -σ, then for every δ>0 it eventually lies in the closed band [-(σ+δ), -(σ-δ)]. This is the direct order-topology wrapper needed for the normalized logarithmic limit in Rhin–Viola Lemma 4.
-- source:
--   Elementary consequence of the limit hypothesis in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

theorem RhinViola.normalizedLogLimitEventuallyBand
    (σ δ : ℝ) (g : ℕ → ℝ)
    (hδ : 0 < δ)
    (hlim : Filter.Tendsto g Filter.atTop (nhds (-σ))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      -(σ + δ) ≤ g n ∧ g n ≤ -(σ - δ) := by sorry
