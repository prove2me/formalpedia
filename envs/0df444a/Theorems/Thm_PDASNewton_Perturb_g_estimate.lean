-- Prove2me | Theorems.Thm_PDASNewton_Perturb_g_estimate
-- name    : PDASNewton.Perturb.g_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:50.756739+00:00
-- url     : https://prove2.me/theorems/1eed004c-2599-4772-970c-7ee356af485b
-- title:
--   Proof of Theorem 3.4, p. 9 — for v ≤ 0, Σᵢ(−A_𝓘⁻¹v)ᵢ ≥ (1−2ρ)/(1−ρ)‖M_𝓘⁻¹v‖₁
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be an M-matrix, $K \in \mathbb{R}^{n\times n}$, $A = M+K$, and let $\rho < \tfrac12$ bound $\|M_{\mathcal{I}}^{-1}K_{\mathcal{I}}\|_1$ for every index set $\mathcal{I}$ ($\|\cdot\|_1$ the maximal absolute column sum). Then for every $\mathcal{I}$ and every $v \in \mathbb{R}^{|\mathcal{I}|}$ with $v \le 0$, the vector $g = -A_{\mathcal{I}}^{-1} v$ satisfies
--   $$\sum_{i\in\mathcal{I}} g_i \;\ge\; \frac{1-2\rho}{1-\rho}\,\big\|M_{\mathcal{I}}^{-1} v\big\|_1 ,$$
--   where $\|w\|_1 = \sum_i |w_i|$.
--
--   In the proof of Theorem 3.4 it is applied with $v = \lambda^k_{\mathcal{I}}$, which is $\le 0$ on the inactive set from the second iteration on; it shows that the multiplier term of (3.8) cannot increase the merit function $\sum_i y^k_i$, and since $\rho<\tfrac12$ the right-hand side is nonnegative.
--
--   **Formalization Note** The page's last occurrence reads $\|M^{-1}\lambda^k_{\mathcal{I}}\|_1$; it is a misprint for $\|M_{\mathcal{I}}^{-1}\lambda^k_{\mathcal{I}}\|_1$, as in the first line of the same display, and the statement uses $M_{\mathcal{I}}^{-1}$. The invertibility of $A_{\mathcal{I}}$ is not assumed: it follows from the hypotheses (preceding milestone).
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 9, proof of Theorem 3.4, display after (3.8) (estimate of Σ gᵢ)

import Mathlib
import Definitions.Def_PDASNewton_Perturb_Setting

open Filter Topology Matrix

namespace PDASNewton.Perturb

theorem g_estimate {n : ℕ} (M K : Matrix (Fin n) (Fin n) ℝ) (hM : IsMMatrix M)
    (ρ : ℝ) (hρ : ∀ S : Finset (Fin n), oneNorm ((PDASNewton.MMatrix.principal M S)⁻¹ * PDASNewton.MMatrix.principal K S) ≤ ρ)
    (hρ_half : ρ < 1 / 2) :
    ∀ (S : Finset (Fin n)) (v : S → ℝ), v ≤ 0 →
      (1 - 2 * ρ) / (1 - ρ) * ∑ i, |((PDASNewton.MMatrix.principal M S)⁻¹ *ᵥ v) i| ≤
        ∑ i, (-((PDASNewton.MMatrix.principal (M + K) S)⁻¹ *ᵥ v)) i := by sorry

end PDASNewton.Perturb
