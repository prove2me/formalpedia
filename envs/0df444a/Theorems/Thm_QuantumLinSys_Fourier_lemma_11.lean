-- Prove2me | Theorems.Thm_QuantumLinSys_Fourier_lemma_11
-- name    : QuantumLinSys.Fourier.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:07.683702+00:00
-- url     : https://prove2.me/theorems/661ba76b-fa0a-4207-99a5-4fa3cdc81356
-- title:
--   Lemma 11, p. 10 — discretized Gaussian Fourier sum is ε-close to 1/x
-- statement:
--   There are positive absolute constants $c,C$ such that, for each condition number $\kappa\ge1$ and accuracy $0<\varepsilon<1/2$, one can choose $J,K\in\mathbb N$ and real mesh widths $\Delta_y,\Delta_z$ satisfying two-sided bounds with those constants:
--   $$
--   J=\Theta\!\left(\frac\kappa\varepsilon\log\frac\kappa\varepsilon\right),\quad
--   K=\Theta\!\left(\kappa\log\frac\kappa\varepsilon\right),\quad
--   \Delta_y=\Theta\!\left(\frac\varepsilon{\sqrt{\log(\kappa/\varepsilon)}}\right),\quad
--   \Delta_z=\Theta\!\left(\frac1{\kappa\sqrt{\log(\kappa/\varepsilon)}}\right).
--   $$
--   For the finite complex Fourier double sum $h$ of (18),
--   $$
--   \left|h(x)-\frac1x\right|\le\varepsilon\qquad(x\in D_\kappa).
--   $$
--
--   This finite expansion is the scalar approximation used in the paper's Fourier approach to quantum linear systems.
--
--   **Formalization Note** One pair $c,C$ works uniformly for all $\kappa,\varepsilon$ and all four scales. The condition-number convention $\kappa\ge1$ and Corollary 10's $0<\varepsilon<1/2$ exclude an empty spectral domain and nonpositive logarithmic scales. The conclusion has exactly $\varepsilon$, rather than an unspecified multiple of it.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 10, Lemma 11 and display (18); proof pp. 13–14

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

namespace QuantumLinSys.Fourier

/-- Lemma 11, p. 10: the finite Fourier double sum (18) approximates 1/x. -/
theorem lemma_11 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ κ ε : ℝ,
      1 ≤ κ → 0 < ε → ε < 1 / 2 →
        ∃ (J K : ℕ) (Δy Δz : ℝ),
          c * (κ / ε * Real.log (κ / ε)) ≤ (J : ℝ) ∧
          (J : ℝ) ≤ C * (κ / ε * Real.log (κ / ε)) ∧
          c * (κ * Real.log (κ / ε)) ≤ (K : ℝ) ∧
          (K : ℝ) ≤ C * (κ * Real.log (κ / ε)) ∧
          c * (ε / Real.sqrt (Real.log (κ / ε))) ≤ Δy ∧
          Δy ≤ C * (ε / Real.sqrt (Real.log (κ / ε))) ∧
          c * (κ * Real.sqrt (Real.log (κ / ε)))⁻¹ ≤ Δz ∧
          Δz ≤ C * (κ * Real.sqrt (Real.log (κ / ε)))⁻¹ ∧
          ∀ x ∈ QuantumLinSys.Chebyshev.Dκ κ, ‖hDisc J K Δy Δz x - ((1 / x : ℝ) : ℂ)‖ ≤ ε := by sorry

end QuantumLinSys.Fourier
