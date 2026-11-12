-- Prove2me | Theorems.Thm_RobustOpt2009_SDPApproximation_theorem_7_1_3_ii
-- name    : RobustOpt2009.SDPApproximation.theorem_7_1_3_ii
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T06:31:16.381133+00:00
-- url     : https://prove2.me/theorems/a3dceb9b-7375-42c0-8878-572c63a2b915
-- title:
--   Theorem 7.1.3 (ii) — rank-sensitive tightness of the real mixed-block Matrix Cube certificate
-- statement:
--   This is part (ii) of the real mixed-block Matrix Cube Theorem (Theorem 7.1.3): the rank-sensitive **tightness** of the semidefinite certificate $\mathcal B(\rho)$.
--
--   Let $B_0,B_1,\ldots,B_s$ be real symmetric $m\times m$ matrices ($m>0$), and let $L_j\in\mathbb R^{p_j\times m}$, $R_j\in\mathbb R^{q_j\times m}$, $j=1,\ldots,f$, with $p_j,q_j>0$. For $r\in\mathbb R$ let $\mathcal A(r)$ be the robust condition
--   $$B_0+\sum_{i=1}^s z_iB_i+\sum_{j=1}^f\bigl(L_j^TZ_jR_j+R_j^TZ_j^TL_j\bigr)\succeq0\qquad\text{for all }|z_i|\le r,\ \|Z_j\|_{2,2}\le r,$$
--   and, for a fixed $\rho\ge0$, let $\mathcal B(\rho)$ ask for symmetric matrices $U_i,V_j$ with
--   $$U_i\succeq\pm B_i,\qquad V_j\succeq L_j^TZR_j+R_j^TZ^TL_j\ \ \forall\,\|Z\|_{2,2}\le1,\qquad B_0-\rho\sum_iU_i-\rho\sum_jV_j\succeq0 .$$
--
--   **Claim.** There is one universal nondecreasing function $\vartheta:\mathbb N\to\mathbb R$ with
--   $$\vartheta(2)=\frac\pi2,\qquad\vartheta(4)=2,\qquad\vartheta(\mu)\le\pi\sqrt{\mu/2}\ \ (\mu\ge2),$$
--   such that for all data as above and every integer $\mu\ge2$ with $\operatorname{rank}B_i\le\mu$ for all $i$:
--   $$\neg\,\mathcal B(\rho)\ \Longrightarrow\ \neg\,\mathcal A(\vartheta(\mu)\rho).$$
--
--   Part (i) of Theorem 7.1.3 (sufficiency $\mathcal B(\rho)\Rightarrow\mathcal A(\rho)$, and exactness for a single perturbation block) is elementary; this child isolates the hard part, whose proof in the book (Appendix B.4.6, Theorem B.4.14) goes through semidefinite duality and Gaussian randomization. The predicates are expanded verbatim as in the parent statement `theorem_7_1_3`; $\|\cdot\|$ is the spectral (L2 operator) norm.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 7.1.3 (ii), printed p. 183 (PDF p. 209); cf. Theorem B.4.14 (iii), printed p. 507

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustOpt2009.SDPApproximation

/-- Theorem 7.1.3 (ii): the rank-sensitive tightness bound of the real mixed-block
Matrix Cube Theorem, with one universal nondecreasing function `θ`. -/
theorem theorem_7_1_3_ii :
    ∃ θ : ℕ → ℝ, Monotone θ ∧ θ 2 = Real.pi / 2 ∧ θ 4 = 2 ∧
      (∀ μ : ℕ, 2 ≤ μ → θ μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2)) ∧
      ∀ (m s f : ℕ), 0 < m → ∀ (p q : Fin f → ℕ),
      (∀ j, 0 < p j) → (∀ j, 0 < q j) →
      ∀ (B₀ : Matrix (Fin m) (Fin m) ℝ) (B : Fin s → Matrix (Fin m) (Fin m) ℝ)
        (L : (j : Fin f) → Matrix (Fin (p j)) (Fin m) ℝ)
        (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ),
      B₀.IsHermitian → (∀ i, (B i).IsHermitian) → ∀ ρ : ℝ, 0 ≤ ρ →
      let a : ℝ → Prop := fun r =>
        ∀ (z : Fin s → ℝ) (Z : (j : Fin f) → Matrix (Fin (p j)) (Fin (q j)) ℝ),
          (∀ i, |z i| ≤ r) → (∀ j, ‖Z j‖ ≤ r) →
          (B₀ + (∑ i, z i • B i) +
            ∑ j, ((L j)ᵀ * Z j * R j + (R j)ᵀ * (Z j)ᵀ * L j)).PosSemidef
      let b : Prop :=
        ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
          (V : Fin f → Matrix (Fin m) (Fin m) ℝ),
          (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
          (∀ i, (U i - B i).PosSemidef ∧ (U i + B i).PosSemidef) ∧
          (∀ j, ∀ Z : Matrix (Fin (p j)) (Fin (q j)) ℝ, ‖Z‖ ≤ 1 →
            (V j - ((L j)ᵀ * Z * R j + (R j)ᵀ * Zᵀ * L j)).PosSemidef) ∧
          (B₀ - ρ • (∑ i, U i) - ρ • (∑ j, V j)).PosSemidef
      ∀ μ : ℕ, 2 ≤ μ → (∀ i, (B i).rank ≤ μ) → ¬ b → ¬ a (θ μ * ρ) := by sorry

end RobustOpt2009.SDPApproximation
