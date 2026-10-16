-- Prove2me | Theorems.Thm_QSPHamSim_Main_rescale_bound
-- name    : QSPHamSim.Main.rescale_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:14.69687+00:00
-- url     : https://prove2.me/theorems/e9467c93-a3fb-449e-aa86-3b48bee942fb
-- title:
--   Eq. (9) — rescaling error and magnitude bounds
-- statement:
--   Suppose real functions $A,C$ approximate the unit-modulus target $e^{ih(\theta)}$ in the sense $|A(\theta)+iC(\theta)-e^{ih(\theta)}|\le\varepsilon$ for every real $\theta$. Put $A_1=A/(1+\varepsilon)$ and $C_1=C/(1+\varepsilon)$. Then
--   $$
--   |A_1+iC_1-e^{ih}|\le2\varepsilon,\qquad A_1^2+C_1^2\le1.
--   $$
--   For $\varepsilon\le1$ the squared magnitude is at least $((1-\varepsilon)/(1+\varepsilon))^2$. If also $h(0)=C(0)=0$, then $(1-\varepsilon)/(1+\varepsilon)\le A_1(0)\le1$; there is an angle $\delta$ with $A_1(0)=\cos\delta\ge(1-\varepsilon)/(1+\varepsilon)$.
--
--   The rescaling makes the approximants eligible for the norm constraint in Theorem 1.
--
--   **Formalization Note** The approximation forces $\varepsilon\ge0$. The upper magnitude bound is implicit in the paper's reason for rescaling; the lower bound requires the stated small-error condition.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 3, Eq. (9) and following paragraph

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem rescale_bound (A C h : ℝ → ℝ) (ε : ℝ)
    (happrox : ∀ θ : ℝ,
      ‖((A θ : ℂ) + (C θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ ε) :
    let A₁ := fun θ : ℝ => A θ / (1 + ε)
    let C₁ := fun θ : ℝ => C θ / (1 + ε)
    (∀ θ : ℝ,
      ‖((A₁ θ : ℂ) + (C₁ θ : ℂ) * Complex.I) -
        Complex.exp ((h θ : ℂ) * Complex.I)‖ ≤ 2 * ε ∧
      A₁ θ ^ 2 + C₁ θ ^ 2 ≤ 1) ∧
    (ε ≤ 1 → ∀ θ : ℝ,
      ((1 - ε) / (1 + ε)) ^ 2 ≤ A₁ θ ^ 2 + C₁ θ ^ 2) ∧
    (h 0 = 0 → C 0 = 0 →
      (1 - ε) / (1 + ε) ≤ A₁ 0 ∧ A₁ 0 ≤ 1 ∧
      ∃ δ : ℝ, Real.cos δ = A₁ 0 ∧
        (1 - ε) / (1 + ε) ≤ Real.cos δ) := by sorry

end QSPHamSim.Main
