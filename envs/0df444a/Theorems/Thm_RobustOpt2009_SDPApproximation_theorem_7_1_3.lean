-- Prove2me | Theorems.Thm_RobustOpt2009_SDPApproximation_theorem_7_1_3
-- name    : RobustOpt2009.SDPApproximation.theorem_7_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:13.394988+00:00
-- url     : https://prove2.me/theorems/254ac67c-14be-4754-ae2e-ea2f897d625c
-- title:
--   Theorem 7.1.3 — Real mixed-block Matrix Cube Theorem
-- statement:
--   Let $B_0,B_1,\ldots,B_s$ be real symmetric $m\times m$ matrices, where $m>0$, and let $L_j\in\mathbb R^{p_j\times m}$, $R_j\in\mathbb R^{q_j\times m}$ for $j=1,\ldots,f$, with positive block dimensions. For $\rho\ge0$, let $\mathcal A(\rho)$ require
--   $$B_0+\sum_i z_iB_i+\sum_j(L_j^TZ_jR_j+R_j^TZ_j^TL_j)\succeq0$$
--   for every $|z_i|\le\rho$, $\|Z_j\|_{2,2}\le\rho$. Let $\mathcal B(\rho)$ ask for symmetric $U_i,V_j$ dominating respectively $\pm B_i$ and every unit-radius full-block perturbation, with $B_0-\rho\sum_iU_i-\rho\sum_jV_j\succeq0$.
--
--   There is a universal nondecreasing function $\vartheta$ such that $\vartheta(2)=\pi/2$, $\vartheta(4)=2$, and $\vartheta(\mu)\le\pi\sqrt{\mu/2}$ for integers $\mu\ge2$. For all the data above:
--   $$\mathcal B(\rho)\Longrightarrow\mathcal A(\rho).$$
--   When $s+f=1$, these conditions are equivalent. Whenever $\mu\ge2$ bounds every scalar matrix rank,
--   $$\neg\mathcal B(\rho)\Longrightarrow\neg\mathcal A(\vartheta(\mu)\rho).$$
--   This is the mixed scalar/full-block result; the existing Open scalar-only Matrix Cube Theorem is not re-posed.
--
--   **Formalization Note** The universal function is chosen before all dimensions and data. The scalar and full block counts may separately be zero. The full-block factors may vanish in this theorem. The finite certificate (9.1.3) is not substituted for the independently defined predicate $\mathcal B$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 7.1.3, printed p. 183 (PDF p. 209)

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustOpt2009.SDPApproximation

/-- Theorem 7.1.3: one universal nondecreasing function, with the two
predicates expanded independently inside the statement. -/
theorem theorem_7_1_3 :
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
      (b → a ρ) ∧ (s + f = 1 → (b ↔ a ρ)) ∧
      (∀ μ : ℕ, 2 ≤ μ → (∀ i, (B i).rank ≤ μ) → ¬ b → ¬ a (θ μ * ρ)) := by sorry

end RobustOpt2009.SDPApproximation
