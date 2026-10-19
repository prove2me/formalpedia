-- Prove2me | Theorems.Thm_SustainableFashion_Variety_proposition_3_iii
-- name    : SustainableFashion.Variety.proposition_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:57.959343+00:00
-- url     : https://prove2.me/theorems/b387d891-6b45-4905-a340-92440783adc8
-- title:
--   Proposition 3(iii), p. 15 — for large γ, thresholds β₁ ≤ β₂ with m* = √(n̄γ/(8β)), m_E, 1
-- statement:
--   Fix admissible parameters with
--   $$\gamma\ge\frac{(k^2-3kk'+4k'^2)^2\theta^2}{2kk'(2k'-k)^3}.$$
--   Then there are thresholds $0<\beta_1\le\beta_2$ such that, when the design cost $\beta$ is varied over $(0,\infty)$ with all other parameters fixed, the optimal number of styles of problem (1) is
--   $$m^*=\begin{cases}\sqrt{\bar n\gamma/(8\beta)}, & \beta<\beta_1,\\ m_E, & \beta_1\le\beta<\beta_2,\\ 1, & \beta\ge\beta_2,\end{cases}$$
--   where $m_E$ is the smallest root on $[1,k'/k]$ of $-\frac{\theta^2k'(k'-km)}{2km^2(2k'-km)^2}+\frac{\gamma}{8m^2}-\frac\beta{\bar n}=0$. Precisely: on each range an optimal solution with the stated $m^*$ exists, and strictly inside each range every optimal solution has that $m^*$.
--
--   **Formalization Note** The thresholds may depend on all parameters other than $\beta$. At $\beta=\beta_1$ and $\beta=\beta_2$ two values of $m$ can be optimal, so uniqueness is asserted only strictly inside the ranges. $\beta_1>0$ is required so that the first range is not empty.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Proposition 3(iii), p. 15 (proof pp. 39–42)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem proposition_3_iii (P : Params) (hP : P.Admissible)
    (hγ : (P.k ^ 2 - 3 * P.k * P.k' + 4 * P.k' ^ 2) ^ 2 * P.θ ^ 2
      / (2 * P.k * P.k' * (2 * P.k' - P.k) ^ 3) ≤ P.γ) :
    ∃ β₁ β₂ : ℝ, 0 < β₁ ∧ β₁ ≤ β₂ ∧ ∀ b : ℝ, 0 < b →
      (b < β₁ → ∃ u q, IsOptimal { P with β := b } (Real.sqrt (P.nbar * P.γ / (8 * b))) u q) ∧
      (b < β₁ → ∀ m u q, IsOptimal { P with β := b } m u q →
        m = Real.sqrt (P.nbar * P.γ / (8 * b))) ∧
      (β₁ ≤ b → b < β₂ → ∃ u q, IsOptimal { P with β := b } (mE { P with β := b }) u q) ∧
      (β₁ < b → b < β₂ → ∀ m u q, IsOptimal { P with β := b } m u q → m = mE { P with β := b }) ∧
      (β₂ ≤ b → ∃ u q, IsOptimal { P with β := b } 1 u q) ∧
      (β₂ < b → ∀ m u q, IsOptimal { P with β := b } m u q → m = 1) := by sorry

end SustainableFashion.Variety
