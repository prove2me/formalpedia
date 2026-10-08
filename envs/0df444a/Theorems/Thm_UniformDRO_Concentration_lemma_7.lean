-- Prove2me | Theorems.Thm_UniformDRO_Concentration_lemma_7
-- name    : UniformDRO.Concentration.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:38.421381+00:00
-- url     : https://prove2.me/theorems/2c32aef2-6ee3-4456-9fd1-e2ac3fb1bda8
-- title:
--   Lemma 7, p. 38 — y ↦ ((1/n)Σ|yᵢ|^{k*})^{1/k*} is n^{−1/(2∨k*)}-Lipschitz for ‖·‖₂
-- statement:
--   Let $k>1$, $k_*=k/(k-1)$ and $n\ge1$. For all $y,y'\in\mathbb R^n$,
--   $$
--   \bigg|\Big(\frac1n\sum_{i=1}^n|y_i|^{k_*}\Big)^{1/k_*}-\Big(\frac1n\sum_{i=1}^n|y'_i|^{k_*}\Big)^{1/k_*}\bigg|\le n^{-1/(2\vee k_*)}\,\|y-y'\|_2 ,
--   $$
--   that is, the normalized $\ell_{k_*}$-norm is $n^{-1/(2\vee k_*)}$-Lipschitz with respect to the Euclidean norm.
--
--   It gives the Lipschitz constant of the plug-in dual objective $g_k(\eta;\widehat P_n)$ as a function of the data, the input to the convex concentration inequality in (28).
--
--   **Formalization Note** The Euclidean distance is written out as $\sqrt{\sum_i(y_i-y'_i)^2}$, because the default norm on `Fin n → ℝ` is the sup norm.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 7, App. C.1, p. 38; proof pp. 38–39

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

namespace UniformDRO.Concentration

/-- Lemma 7 (Duchi & Namkoong, arXiv:1810.08750v6, App. C.1, p. 38): the map
`y ↦ ((1/n) ∑ᵢ |yᵢ|^{k*})^{1/k*}` on `ℝⁿ` is `n^{-1/(2 ∨ k*)}`-Lipschitz for the Euclidean norm.
The Euclidean distance is written out as `√(∑ᵢ (yᵢ - y'ᵢ)²)`, since the default norm on
`Fin n → ℝ` is the sup norm. -/
theorem lemma_7 (k : ℝ) (hk : 1 < k) (n : ℕ) (hn : 0 < n) (y y' : Fin n → ℝ) :
    |((1 / n : ℝ) * ∑ i, |y i| ^ kstar k) ^ (1 / kstar k) -
        ((1 / n : ℝ) * ∑ i, |y' i| ^ kstar k) ^ (1 / kstar k)| ≤
      (n : ℝ) ^ (-(1 / max 2 (kstar k))) * Real.sqrt (∑ i, (y i - y' i) ^ 2) := by sorry

end UniformDRO.Concentration
