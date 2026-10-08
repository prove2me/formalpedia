-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_le_cam_37
-- name    : UniformDRO.LowerBound.le_cam_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:23.918864+00:00
-- url     : https://prove2.me/theorems/664a47b1-b975-44aa-9d3d-d41895d8ccae
-- title:
--   (37), p. 45 — Le Cam: |R_k(P₀) − R_k(P₁)| ≥ 2δ > 0 implies 𝔐ₙ(𝒫, f_k) ≥ (δ/2)(1 − ‖P₀ⁿ − P₁ⁿ‖_TV)
-- statement:
--   Let $k > 1$, $\rho > 0$, $M > 0$ and $n \ge 0$. Let $P_0, P_1$ be laws on $\{0, M\}$ with masses $p_0, p_1 \in [0,1]$ at $M$, and let $\mathcal R_k(P_v)$ denote the Cressie–Read robust risk of $Z \sim P_v$. If
--   $$|\mathcal R_k(P_0) - \mathcal R_k(P_1)| \ge 2\delta > 0,$$
--   then the minimax risk (16) satisfies
--   $$\mathfrak M_n(\mathcal P, f_k) \ge \frac{\delta}{2}\bigl(1 - \|P_0^n - P_1^n\|_{\mathrm{TV}}\bigr). \qquad (37)$$
--
--   This is Le Cam's reduction from estimation to testing: an estimator accurate to within $\delta$ under both laws would distinguish them from $n$ samples, which the total variation between the product laws forbids. Both branches of Theorem 3 are obtained by applying (37) to two well-chosen laws.
--
--   **Formalization Note.** $\mathfrak M_n$ and the total variation are those of the mission's definition file (finite sums over $\{0,M\}^n$; $\mathfrak M_n$ in $[0,\infty]$). The left side is embedded in $[0,\infty]$ with negative values sent to $0$, which loses nothing since $\|\cdot\|_{\mathrm{TV}} \le 1$.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 3 (App. D.1), p. 45, (37)

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem le_cam_37 (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (M : ℝ) (hM : 0 < M) (n : ℕ)
    (p₀ p₁ δ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (hp₁ : p₁ ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ)
    (hsep : 2 * δ ≤ |UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₀) id -
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id|) :
    ENNReal.ofReal (δ / 2 * (1 - tvDist n p₀ p₁)) ≤ minimaxRisk k ρ M n := by sorry

end UniformDRO.LowerBound
