-- Prove2me | Theorems.Thm_QSPHamSim_Main_sos_completion
-- name    : QSPHamSim.Main.sos_completion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:19.188858+00:00
-- url     : https://prove2.me/theorems/06d86686-b950-461e-ae86-16f3d87165a9
-- title:
--   p. 3 — sum-of-squares completion of the Pauli components
-- statement:
--   Let $A_1$ be a real cosine series and $C_1$ a real sine series, both of degree at most $M$, with $A_1(\theta)^2+C_1(\theta)^2\le1$ at every real angle. There are a cosine series $B$ and a sine series $D$ of the same degree such that
--   $$
--   A_1(\theta)^2+B(\theta)^2+C_1(\theta)^2+D(\theta)^2=1.
--   $$
--   Consequently $A_1(0)^2+B(0)^2=1$, and for any angle $\delta$ with $\cos\delta=A_1(0)$, one has $|B(0)|=|\sin\delta|$. This completes the partially specified response to the four real components of a unitary qubit response.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, p. 3, after Eq. (9), before Eq. (10)

import Mathlib
import Definitions.Def_QSPHamSim_Main_Setting

set_option autoImplicit false

namespace QSPHamSim.Main

theorem sos_completion (M : ℕ) (A₁ C₁ : ℝ → ℝ)
    (hA : IsCosSeries M A₁) (hC : IsSinSeries M C₁)
    (hunit : ∀ θ : ℝ, A₁ θ ^ 2 + C₁ θ ^ 2 ≤ 1) :
    ∃ B D : ℝ → ℝ,
      IsCosSeries M B ∧ IsSinSeries M D ∧
      (∀ θ : ℝ, A₁ θ ^ 2 + B θ ^ 2 + C₁ θ ^ 2 + D θ ^ 2 = 1) ∧
      A₁ 0 ^ 2 + B 0 ^ 2 = 1 ∧
      (∀ δ : ℝ, Real.cos δ = A₁ 0 →
        |B 0| = |Real.sin δ|) := by sorry

end QSPHamSim.Main
