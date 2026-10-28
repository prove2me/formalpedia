-- Prove2me | Theorems.Thm_QPurityAmp_Choi_eq_S23
-- name    : QPurityAmp.Choi.eq_S23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:35.772311+00:00
-- url     : https://prove2.me/theorems/cade753e-02f4-485f-8b87-75e0f5005eab
-- title:
--   Eq. (S23), p. 19 — |ψ⟩⟨ψ| = A(−ρ⁻¹) + B I/d with A = λ(d(1−λ)+λ)/(d²(1−λ)), B = d + λ/(1−λ), ρ = D_λ(|ψ⟩⟨ψ|)
-- statement:
--   Let $d\ge 1$, $0<\lambda<1$, and let $\psi\in\mathbb C^d$ be a unit vector with depolarized state $\rho=\mathcal D_\lambda(|\psi\rangle\langle\psi|)=(1-\lambda)|\psi\rangle\langle\psi|+\lambda\,\mathbb I_d/d$. Then $\rho$ is invertible and
--   $$|\psi\rangle\langle\psi|=A\,(-\rho^{-1})+B\,\frac{\mathbb I_d}{d},\qquad A=\frac{\lambda\,(d(1-\lambda)+\lambda)}{d^2(1-\lambda)},\quad B=d+\frac{\lambda}{1-\lambda}.$$
--
--   This identity expresses the pure target state through the inverse of the noisy state. Integrated against $\rho^{\otimes n}$ over the Haar measure it gives $C=AC'+B\,\frac{\mathbb I_d}{d}\otimes\int\rho^{\otimes n}$, which is how the cost matrix $C$ is traded for the more symmetric $C'$.
--
--   **Formalization Note** The invertibility of $\rho$ is part of the conclusion, so the matrix inverse is not Mathlib's junk value.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 19, text above Eq. (S23) and Eq. (S23)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix

/-- Eq. (S23), first relation, p. 19: for the depolarized state ρ = D_λ(|ψ⟩⟨ψ|) with
0 < λ < 1, ρ is invertible and |ψ⟩⟨ψ| = A(−ρ⁻¹) + B I_d/d with
A = λ(d(1−λ)+λ)/(d²(1−λ)) and B = d + λ/(1−λ). -/
theorem eq_S23 {d : ℕ} [NeZero d] (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (psi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) :
    IsUnit (depol d lam (pureProj psi)) ∧
      pureProj psi =
        ((lam * (d * (1 - lam) + lam) / ((d : ℝ) ^ 2 * (1 - lam)) : ℝ) : ℂ) •
            (-(depol d lam (pureProj psi))⁻¹) +
          (((d + lam / (1 - lam)) / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by sorry

end QPurityAmp.Choi
