-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_A_1
-- name    : SKHessianAscent.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:21:56.899807+00:00
-- url     : https://prove2.me/theorems/ada5240c-65f3-4fdc-a4ac-784d863723bd
-- title:
--   Lemma A.1 — bounds on differences of resolvent products $\Delta R$, $\Delta(R^k)$, $\Delta(DR)$, $\Delta(DR^k)$, $\Delta(DR^kD)$
-- statement:
--   Let $W_0,W_1\in\mathbb R^{n\times n}$ be invertible symmetric matrices and $M_0,M_1\in\mathbb C^{n\times n}$. Suppose that for $j=0,1$
--
--   $$
--   \min\mathrm{Spec}\big(|M_j+W_j^{-1}|\big)\ge\gamma,\qquad\|M_j\|_{\mathrm{op}}\le C_1,
--   $$
--
--   where $\gamma>0$, $C_1\ge0$, and put $C_2=(\gamma+C_1)\gamma^{-1}$. Let $D(W)=W^{-1}$, $X(W,M)=M+D(W)$, $R(W,M)=X(W,M)^{-1}$, and for a function $g$ of $(W,M)$ write $\Delta g=g(W_1,M_1)-g(W_0,M_0)$. Then, in the normalized Schatten 2-norm $\|\cdot\|_{L^2}$:
--
--   1. $\|\Delta R\|_{L^2}\le\gamma^{-2}\|\Delta M\|_{L^2}+C_2^2\|\Delta W\|_{L^2}$;
--   2. for $k\ge1$: $\|\Delta(R^k)\|_{L^2}\le k\gamma^{-(k+1)}\|\Delta M\|_{L^2}+kC_2^2\gamma^{-(k-1)}\|\Delta W\|_{L^2}$;
--   3. $\|\Delta(DR)\|_{L^2}\le C_2\gamma^{-1}\|\Delta M\|_{L^2}+C_1C_2^2\|\Delta W\|_{L^2}$;
--   4. for $k\ge1$: $\|\Delta(DR^k)\|_{L^2}\le kC_2\gamma^{-k}\|\Delta M\|_{L^2}+(kC_2-1)C_2^2\gamma^{-(k-2)}\|\Delta W\|_{L^2}$;
--   5. for $k\ge2$: $\|\Delta(DR^kD)\|_{L^2}\le kC_2^2\gamma^{-(k-1)}\|\Delta M\|_{L^2}+(kC_2-2)C_2^3\gamma^{-(k-3)}\|\Delta W\|_{L^2}$.
--
--   These finite-difference estimates replace derivative bounds for resolvent products, and are what allows Lipschitz estimates on a non-convex set.
--
--   **Formalization Note** $\min\mathrm{Spec}(|X|)\ge\gamma$ is stated as $\|Xv\|_2\ge\gamma\|v\|_2$ for all $v\in\mathbb C^n$ (smallest singular value at least $\gamma$). Powers of $\gamma$ with possibly negative exponents are integer powers. The paper's statement also fixes a matrix $T$ that does not occur in parts (a)–(e); it is omitted.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma A.1, p. 45

import Mathlib
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Resolvent

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_A_1 {n : ℕ} (W₀ W₁ : Matrix (Fin n) (Fin n) ℝ)
    (hW₀ : W₀.IsSymm) (hW₁ : W₁.IsSymm) (hU₀ : IsUnit W₀.det) (hU₁ : IsUnit W₁.det)
    (M₀ M₁ : Matrix (Fin n) (Fin n) ℂ) (γ C₁ : ℝ) (hγ : 0 < γ) (hC₁ : 0 ≤ C₁)
    (hg₀ : ∀ v : EuclideanSpace ℂ (Fin n),
      γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (M₀ + toC W₀⁻¹) v‖)
    (hg₁ : ∀ v : EuclideanSpace ℂ (Fin n),
      γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (M₁ + toC W₁⁻¹) v‖)
    (hM₀ : cOpNorm M₀ ≤ C₁) (hM₁ : cOpNorm M₁ ≤ C₁) :
    let C₂ : ℝ := (γ + C₁) * γ⁻¹
    let D₀ := toC W₀⁻¹
    let D₁ := toC W₁⁻¹
    let R₀ := (M₀ + D₀)⁻¹
    let R₁ := (M₁ + D₁)⁻¹
    let dM : ℝ := cSchatten2 (M₁ - M₀)
    let dW : ℝ := schatten2 (W₁ - W₀)
    cSchatten2 (R₁ - R₀) ≤ γ ^ (-2 : ℤ) * dM + C₂ ^ 2 * dW ∧
    (∀ k : ℕ, 1 ≤ k →
      cSchatten2 (R₁ ^ k - R₀ ^ k) ≤
        k * γ ^ (-(k : ℤ) - 1) * dM + k * C₂ ^ 2 * γ ^ (-(k : ℤ) + 1) * dW) ∧
    cSchatten2 (D₁ * R₁ - D₀ * R₀) ≤ C₂ * γ ^ (-1 : ℤ) * dM + C₁ * C₂ ^ 2 * dW ∧
    (∀ k : ℕ, 1 ≤ k →
      cSchatten2 (D₁ * R₁ ^ k - D₀ * R₀ ^ k) ≤
        k * C₂ * γ ^ (-(k : ℤ)) * dM + (k * C₂ - 1) * C₂ ^ 2 * γ ^ (-(k : ℤ) + 2) * dW) ∧
    (∀ k : ℕ, 2 ≤ k →
      cSchatten2 (D₁ * R₁ ^ k * D₁ - D₀ * R₀ ^ k * D₀) ≤
        k * C₂ ^ 2 * γ ^ (-(k : ℤ) + 1) * dM +
          (k * C₂ - 2) * C₂ ^ 3 * γ ^ (-(k : ℤ) + 3) * dW) := by sorry

end SKHessianAscent
