-- Prove2me | Theorems.Thm_RobustOpt2009_SDPApproximation_theorem_9_1_2
-- name    : RobustOpt2009.SDPApproximation.theorem_9_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:10.701632+00:00
-- url     : https://prove2.me/theorems/96682542-a291-4474-9916-e8966ac4d9d0
-- title:
--   Theorem 9.1.2 — Rank-sensitive approximation of structured robust LMIs
-- statement:
--   Consider the real uncertain LMI of Definition 9.1.1, with positive matrix and full-block dimensions, $s+f\ge1$ perturbation blocks, and radius $\rho>0$. Its nominal matrix $A^n(y)$, scalar coefficient matrices $A_i(y)$ and full-block factors $L_j(y)$ are affine in $y\in\mathbb R^n$; the nominal and scalar matrices are symmetric and each fixed $R_j$ is nonzero. Robust feasibility $\mathcal A_y(\rho)$ means
--   $$A^n(y)+\sum_i z_iA_i(y)+\sum_j[L_j(y)^TZ_jR_j+R_j^TZ_j^TL_j(y)]\succeq0$$
--   for all $|z_i|\le\rho$ and $\|Z_j\|_{2,2}\le\rho$. Let $\mathcal C_y(\rho)$ be feasibility in symmetric matrices $U_i,V_j$ and real scalars $\lambda_j$ of
--   $$U_i\succeq\pm A_i(y),\quad
--   \begin{bmatrix}\lambda_jI_{p_j}&L_j(y)\\L_j(y)^T&V_j-\lambda_jR_j^TR_j\end{bmatrix}\succeq0,\quad
--   A^n(y)-\rho\left(\sum_iU_i+\sum_jV_j\right)\succeq0.$$
--   There is one universal function $\vartheta$ with
--   $$\vartheta(2)=\pi/2,\qquad\vartheta(4)=2,\qquad\vartheta(\mu)\le\pi\sqrt{\mu/2}\quad(\mu>2)$$
--   such that for every instance and every design vector:
--
--   1. $\mathcal C_y(\rho)$ implies $\mathcal A_y(\rho)$: the finite LMI system is safe.
--   2. If $\mu$ is the least integer at least two bounding all $\operatorname{rank}A_i(y')$ uniformly over every $i,y'$, then
--   $$\neg\mathcal C_y(\rho)\Longrightarrow\neg\mathcal A_y(\vartheta(\mu)\rho).$$
--   3. $\mathcal C_y(\rho)$ and $\mathcal A_y(\rho)$ are equivalent if there is one perturbation block, or if every block is scalar and every $A_i(y')$ has rank at most one.
--
--   The theorem gives a safe SDP approximation with rank-sensitive tightness and identifies two exact regimes.
--
--   **Formalization Note** Tractability is represented by the displayed finite system of affine LMIs and its existential projection onto $y$, with fixed $\rho$; no algorithmic complexity model is asserted. Scalar and full indices are re-enumerated separately. The least rank bound quantifies over all design vectors, and the same existential $\vartheta$ precedes every instance parameter. The main theorem's printed bound $\pi\sqrt{\mu/2}$ is retained.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 9.1.2, printed pp. 225–226 (PDF pp. 251–252), (9.1.3)–(9.1.4)

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustOpt2009.SDPApproximation

/-- Theorem 9.1.2. All data and predicates are expanded here so that the
statement is independently readable without consulting an imported definition. -/
theorem theorem_9_1_2 :
    ∃ θ : ℕ → ℝ, θ 2 = Real.pi / 2 ∧ θ 4 = 2 ∧
      (∀ μ : ℕ, 2 < μ → θ μ ≤ Real.pi * Real.sqrt ((μ : ℝ) / 2)) ∧
      ∀ (n m s f : ℕ), 0 < m → 0 < s + f →
      ∀ (p q : Fin f → ℕ), (∀ j, 0 < p j) → (∀ j, 0 < q j) →
      ∀ (A₀ : (Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ)
        (A : Fin s → ((Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin m) (Fin m) ℝ))
        (L : (j : Fin f) → ((Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin (p j)) (Fin m) ℝ))
        (R : (j : Fin f) → Matrix (Fin (q j)) (Fin m) ℝ),
      (∀ y, (A₀ y).IsHermitian) → (∀ i y, (A i y).IsHermitian) →
      (∀ j, R j ≠ 0) → ∀ (ρ : ℝ), 0 < ρ → ∀ y : Fin n → ℝ,
      let RC : ℝ → Prop := fun r =>
        ∀ (z : Fin s → ℝ) (Z : (j : Fin f) → Matrix (Fin (p j)) (Fin (q j)) ℝ),
          (∀ i, |z i| ≤ r) → (∀ j, ‖Z j‖ ≤ r) →
          (A₀ y + (∑ i, z i • A i y) +
            ∑ j, ((L j y)ᵀ * Z j * R j + (R j)ᵀ * (Z j)ᵀ * L j y)).PosSemidef
      let SDP : Prop :=
        ∃ (U : Fin s → Matrix (Fin m) (Fin m) ℝ)
          (V : Fin f → Matrix (Fin m) (Fin m) ℝ) (lam : Fin f → ℝ),
          (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
          (∀ i, (U i - A i y).PosSemidef ∧ (U i + A i y).PosSemidef) ∧
          (∀ j, (fromBlocks (lam j • (1 : Matrix (Fin (p j)) (Fin (p j)) ℝ))
            (L j y) (L j y)ᵀ (V j - lam j • ((R j)ᵀ * R j))).PosSemidef) ∧
          (A₀ y - ρ • ((∑ i, U i) + ∑ j, V j)).PosSemidef
      (SDP → RC ρ) ∧
      (∀ μ : ℕ, IsLeast {k : ℕ | 2 ≤ k ∧ ∀ i y', (A i y').rank ≤ k} μ →
        ¬ SDP → ¬ RC (θ μ * ρ)) ∧
      ((s + f = 1 ∨ (f = 0 ∧ ∀ i y', (A i y').rank ≤ 1)) → (SDP ↔ RC ρ)) := by sorry

end RobustOpt2009.SDPApproximation
