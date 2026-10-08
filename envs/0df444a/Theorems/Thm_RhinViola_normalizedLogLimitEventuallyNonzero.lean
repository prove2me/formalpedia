-- Prove2me | Theorems.Thm_RhinViola_normalizedLogLimitEventuallyNonzero
-- name    : RhinViola.normalizedLogLimitEventuallyNonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T17:13:53.889858+00:00
-- url     : https://prove2.me/theorems/e7f18ab2-c20c-4f15-b637-da1d31ae55d5
-- title:
--   A negative normalized logarithmic limit forces eventual nonvanishing
-- statement:
--   If σ>0 and log|f_n|/n tends to -σ, then f_n is nonzero for all sufficiently large n. Indeed the normalized logarithm is eventually strictly below the negative number -σ/2, whereas f_n=0 would make that term zero.
-- source:
--   Elementary consequence of the nonzero exponential decay limit in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

theorem RhinViola.normalizedLogLimitEventuallyNonzero
    (σ : ℝ) (f : ℕ → ℝ)
    (hσ : 0 < σ)
    (hlim : Filter.Tendsto
      (fun n : ℕ => Real.log |f n| / (n : ℝ))
      Filter.atTop (nhds (-σ))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≠ 0 := by sorry
