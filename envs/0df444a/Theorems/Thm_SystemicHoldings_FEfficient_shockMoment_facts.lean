-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_shockMoment_facts
-- name    : SystemicHoldings.FEfficient.shockMoment_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:16.76324+00:00
-- url     : https://prove2.me/theorems/2f41a8b7-ac5c-456a-a36f-22a34122cb26
-- title:
--   Proof of Lemma 4.1, EC p. 6 — G is positive definite, Sherman–Morrison form of G⁻¹, and 1ᵀG⁻¹1 ≠ 0
-- statement:
--   Let $K\ge 1$, $\mu\in\mathbb R^K$, and $\sigma\in\mathbb R^K$ with $\sigma_k>0$ for all $k$. Let $G=\mu\mu^\top+\mathrm{Diag}(\sigma^2)$ and write $\mu/\sigma^2$ and $1/\sigma^2$ for the componentwise quotients. Then
--
--   1. $G$ is symmetric positive definite;
--   2. its inverse is given by the Sherman–Morrison formula
--   $$G^{-1} = \mathrm{Diag}\Big(\frac{1}{\sigma^2}\Big) - \frac{\frac{\mu}{\sigma^2}\big(\frac{\mu}{\sigma^2}\big)^\top}{1+\big(\frac{\mu}{\sigma^2}\big)^\top\mu};$$
--   3. $$\mathbf 1_K^\top G^{-1}\mathbf 1_K = \Big(\frac{1}{\sigma^2}\Big)^\top\mathbf 1_K - \frac{\big(\mathbf 1_K^\top \frac{\mu}{\sigma^2}\big)^2}{1+\big(\frac{\mu}{\sigma^2}\big)^\top\mu};$$
--   4. $\mathbf 1_K^\top G^{-1}\mathbf 1_K\neq 0$.
--
--   These facts make the vector $z=G^{-1}\mathbf 1_K$ and the scalar $\mathbf 1_K^\top z$ in Lemma 4.1 well defined and nonzero, which every later formula divides by.
--
--   **Formalization Note** $K\ge1$ is added: for $K=0$ the sum $\mathbf 1_K^\top G^{-1}\mathbf 1_K$ is empty and equals $0$. Positive definiteness is Mathlib's `Matrix.PosDef` (which includes symmetry).
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, E-Companion p. 6 (PDF 36), proof of Lemma 4.1 (EC.1.3.2)

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem shockMoment_facts {K : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k) :
    (shockMoment μ σ).PosDef ∧
    (shockMoment μ σ)⁻¹ =
      diagonal (fun k => 1 / σ k ^ 2) -
        (1 / (1 + (fun k => μ k / σ k ^ 2) ⬝ᵥ μ)) •
          vecMulVec (fun k => μ k / σ k ^ 2) (fun k => μ k / σ k ^ 2) ∧
    (fun _ => (1 : ℝ)) ⬝ᵥ ((shockMoment μ σ)⁻¹ *ᵥ (fun _ => (1 : ℝ))) =
      (fun k => 1 / σ k ^ 2) ⬝ᵥ (fun _ => (1 : ℝ)) -
        ((fun _ => (1 : ℝ)) ⬝ᵥ (fun k => μ k / σ k ^ 2)) ^ 2 /
          (1 + (fun k => μ k / σ k ^ 2) ⬝ᵥ μ) ∧
    (fun _ => (1 : ℝ)) ⬝ᵥ ((shockMoment μ σ)⁻¹ *ᵥ (fun _ => (1 : ℝ))) ≠ 0 := by sorry

end SystemicHoldings.FEfficient
