-- Prove2me | Theorems.Thm_QSPHamSim_Main_rotation_bound
-- name    : QSPHamSim.Main.rotation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:16.227181+00:00
-- url     : https://prove2.me/theorems/71c1c79f-9dce-406c-9e65-4b6bb7983620
-- title:
--   Eq. (10) — bound for the final rotation of A
-- statement:
--   Assume $0\le\varepsilon\le1$ and real functions $A_1,B,C_1,D$ have squared values summing to one. Suppose $A_1^2+C_1^2$ is at least $((1-\varepsilon)/(1+\varepsilon))^2$ everywhere. Choose an angle $\delta$ with $\cos\delta=A_1(0)$, $\sin\delta=B(0)$ and $\cos\delta\ge(1-\varepsilon)/(1+\varepsilon)$. Define $A_2=A_1\cos\delta+B\sin\delta$. Then
--   $$
--   B^2\le\frac{4\varepsilon}{(1+\varepsilon)^2},\qquad |A_2-A_1|\le\frac{2\varepsilon}{1+\varepsilon}+|B|\frac{2\sqrt\varepsilon}{1+\varepsilon}\le6\varepsilon.
--   $$
--   These inequalities control the extra error incurred while adjusting the response at zero.
--
--   **Formalization Note** The sign choice $\sin\delta=B(0)$ makes the paper's later equality $A_2(0)=1$ precise.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, pp. 3–4, Eq. (10) and paragraph following it

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem rotation_bound (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A₁ B C₁ D : ℝ → ℝ)
    (hunit : ∀ θ : ℝ,
      A₁ θ ^ 2 + B θ ^ 2 + C₁ θ ^ 2 + D θ ^ 2 = 1)
    (hlower : ∀ θ : ℝ,
      ((1 - ε) / (1 + ε)) ^ 2 ≤ A₁ θ ^ 2 + C₁ θ ^ 2)
    (δ : ℝ) (hcos : Real.cos δ = A₁ 0)
    (hsin : Real.sin δ = B 0)
    (hδ : (1 - ε) / (1 + ε) ≤ Real.cos δ) :
    let A₂ := fun θ : ℝ => A₁ θ * Real.cos δ + B θ * Real.sin δ
    ∀ θ : ℝ,
      B θ ^ 2 ≤ 4 * ε / (1 + ε) ^ 2 ∧
      |A₂ θ - A₁ θ| ≤
        2 * ε / (1 + ε) + |B θ| * (2 * Real.sqrt ε / (1 + ε)) ∧
      |A₂ θ - A₁ θ| ≤ 6 * ε := by sorry

end QSPHamSim.Main
