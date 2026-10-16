-- Prove2me | Theorems.Thm_QSPHamSim_Main_error_and_success
-- name    : QSPHamSim.Main.error_and_success
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:16.374157+00:00
-- url     : https://prove2.me/theorems/e6c4d7ab-2534-41b6-8b91-de09b9a78cec
-- title:
--   Eq. (11) — final scalar error and success bound
-- statement:
--   Suppose $A_1+iC_1$ approximates $e^{ih}$ to error at most $2\varepsilon$ and $|A_2-A_1|\le6\varepsilon$, pointwise in the angle. Then
--   $$
--   |A_2+iC_1-e^{ih}|\le8\varepsilon,\qquad |A_2+iC_1|^2\ge1-16\varepsilon.
--   $$
--   When $8\varepsilon\le1$, the stronger intermediate bound $|A_2+iC_1|^2\ge(1-8\varepsilon)^2$ also holds.
--
--   This combines the two approximation errors and supplies the paper's success-probability constant.
--
--   **Formalization Note** Squaring the lower modulus bound requires $8\varepsilon\le1$; the stated $1-16\varepsilon$ bound remains valid without that restriction.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 4, Eq. (11)

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem error_and_success (A₁ A₂ C₁ h : ℝ → ℝ) (ε : ℝ)
    (hfirst : ∀ θ : ℝ,
      ‖((A₁ θ : ℂ) + (C₁ θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ 2 * ε)
    (hsecond : ∀ θ : ℝ, |A₂ θ - A₁ θ| ≤ 6 * ε) :
    ∀ θ : ℝ,
      ‖((A₂ θ : ℂ) + (C₁ θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ 8 * ε ∧
      1 - 16 * ε ≤ ‖((A₂ θ : ℂ) + (C₁ θ : ℂ) * Complex.I)‖ ^ 2 ∧
      (8 * ε ≤ 1 →
        (1 - 8 * ε) ^ 2 ≤
          ‖((A₂ θ : ℂ) + (C₁ θ : ℂ) * Complex.I)‖ ^ 2) := by sorry

end QSPHamSim.Main
