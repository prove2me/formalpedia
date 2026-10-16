-- Prove2me | Theorems.Thm_QSPHamSim_Main_rotated_satisfies_thm1
-- name    : QSPHamSim.Main.rotated_satisfies_thm1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:16.20499+00:00
-- url     : https://prove2.me/theorems/99e7cfa3-7e0e-4aa4-aad0-13f4a4ada29c
-- title:
--   p. 4 — rotated pair satisfies Theorem 1
-- statement:
--   Let $A_1$ and $B$ be cosine series of degree at most $M$, and let $C_1$ and $D$ be sine series of that degree. Suppose their four squares sum to one at every angle. Choose $\delta$ with $\cos\delta=A_1(0)$ and $\sin\delta=B(0)$, and put $A_2=A_1\cos\delta+B\sin\delta$. Then
--   $$
--   A_2(0)=1,\qquad A_2(\theta)^2+C_1(\theta)^2\le1\quad(\theta\in\mathbb R),
--   $$
--   and $A_2$ remains a cosine series of degree at most $M$. The already assumed sine-series form of $C_1$ completes conditions (1)–(4) of Theorem 1 for the pair $(A_2,C_1)$.
--
--   This is the paper's final eligibility check before phases are chosen. The matching sign of $\sin\delta$ ensures the zero-angle equality.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 4, first paragraph before Eq. (11)

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem rotated_satisfies_thm1 (M : ℕ) (A₁ B C₁ D : ℝ → ℝ)
    (hA : IsCosSeries M A₁) (hB : IsCosSeries M B)
    (hC : IsSinSeries M C₁) (hD : IsSinSeries M D)
    (hunit : ∀ θ : ℝ,
      A₁ θ ^ 2 + B θ ^ 2 + C₁ θ ^ 2 + D θ ^ 2 = 1)
    (δ : ℝ) (hcos : Real.cos δ = A₁ 0)
    (hsin : Real.sin δ = B 0) :
    let A₂ := fun θ : ℝ => A₁ θ * Real.cos δ + B θ * Real.sin δ
    A₂ 0 = 1 ∧ IsCosSeries M A₂ ∧
      (∀ θ : ℝ, A₂ θ ^ 2 + C₁ θ ^ 2 ≤ 1) := by sorry

end QSPHamSim.Main
