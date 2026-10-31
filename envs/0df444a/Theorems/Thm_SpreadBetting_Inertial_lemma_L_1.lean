-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_L_1
-- name    : SpreadBetting.Inertial.lemma_L_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:38.323986+00:00
-- url     : https://prove2.me/theorems/5e2fa1f7-67d0-45df-a501-cabe0beb9724
-- title:
--   Lemma L.1, p. 70 — Σ_n Π_{m≤n} (½ − x_m)/(½ + x_m) converges if liminf n xₙ > ¼ and diverges if limsup n xₙ < ¼
-- statement:
--   Let $(x_n)_{n \in \mathbb Z_+}$ satisfy $x_n \in (0, \tfrac12)$ for all $n$, and let
--   $$
--   y_n := \prod_{m=1}^n \frac{\tfrac12 - x_m}{\tfrac12 + x_m}.
--   $$
--   1. If $\liminf_{n\to\infty} n x_n > \tfrac14$, then $\sum_n y_n$ converges.
--   2. If $\limsup_{n\to\infty} n x_n < \tfrac14$, then $\sum_n y_n$ diverges.
--
--   This is a Raabe-type test; with $x_n = \rho(n)$ it separates the transient (slowly vanishing) from the recurrent (fast vanishing) residual probability sequences.
--
--   **Formalization Note** The liminf and limsup are taken in `EReal`. The sequence is indexed by $\mathbb N$; $y_0 = 1$ is an empty product and does not affect convergence. Since $y_n > 0$, divergence is stated as non-summability.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 70, Lemma L.1

import Mathlib

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_L_1 (x : ℕ → ℝ) (hx : ∀ n : ℕ, 1 ≤ n → x n ∈ Set.Ioo 0 (1 / 2)) :
    let y : ℕ → ℝ := fun n => ∏ m ∈ Finset.Icc 1 n, (1 / 2 - x m) / (1 / 2 + x m)
    ((1 / 4 : EReal) < Filter.liminf (fun n : ℕ => ((n * x n : ℝ) : EReal)) atTop →
      Summable y) ∧
    (Filter.limsup (fun n : ℕ => ((n * x n : ℝ) : EReal)) atTop < (1 / 4 : EReal) →
      ¬ Summable y) := by sorry

end SpreadBetting.Inertial
