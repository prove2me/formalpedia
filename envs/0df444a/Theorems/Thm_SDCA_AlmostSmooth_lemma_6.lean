-- Prove2me | Theorems.Thm_SDCA_AlmostSmooth_lemma_6
-- name    : SDCA.AlmostSmooth.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:06:29.460974+00:00
-- url     : https://prove2.me/theorems/7bbf117c-078d-4a30-a2d0-afd2b07e8e1d
-- title:
--   Lemma 6 — for $L$-Lipschitz losses, $G_*(s)\le 4L^2N(s/(\lambda n))/n$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $\|x_i\|\le1$, let each $\varphi_i:\mathbb R\to\mathbb R$ be $L$-Lipschitz, let $\lambda>0$, and let $\gamma_1,\dots,\gamma_n\ge0$. Let $\alpha$ and $\alpha^*$ be feasible dual variables (all $\varphi_i^*(-\alpha_i)$ and $\varphi_i^*(-\alpha_i^*)$ finite). For $s>0$ put
--   $$
--   G_*(s)=\frac1n\sum_{i=1}^n\Bigl(\|x_i\|^2-\frac{\gamma_i\lambda n}{s}\Bigr)(\alpha_i^*-\alpha_i)^2
--   $$
--   and $N(u)=\#\{i:\gamma_i<u\}$. Then
--   $$
--   G_*(s)\le\frac{4L^2\,N\bigl(s/(\lambda n)\bigr)}{n}.
--   $$
--
--   Only the coordinates with $\gamma_i<s/(\lambda n)$ can contribute positively to $G_*(s)$; when few constants $\gamma_i$ are small, the variance term of Lemma 5 is small, which is what makes the rate of Theorem 5 better than that of Theorem 1.
--
--   **Formalization Note** The statement is conditional on the dual point $\alpha$ (the paper's $\alpha^{(t-1)}$ averaged over the history gives its $G_*^{(t)}(s)$). The bound $\|x_i\|^2\le1$ is the paper's standing assumption, used in its proof. The paper's "$s\in[0,1]$" is replaced by $s>0$, which is where $\gamma_i\lambda n/s$ is defined.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 20, Lemma 6

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model

namespace SDCA.AlmostSmooth

/-- Lemma 6 (p. 20), in conditional form: if every `φᵢ` is `L`-Lipschitz, `‖xᵢ‖ ≤ 1`, `γᵢ ≥ 0`,
and `α`, `α*` are feasible dual points, then for every `s > 0`
`G*(s) = (1/n) ∑ᵢ (‖xᵢ‖² − γᵢλn/s)(α*ᵢ − αᵢ)² ≤ 4L² N(s/(λn))/n`, where `N(u) = #{i : γᵢ < u}`. -/
theorem lemma_6 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, ‖x i‖ ≤ 1) (φ : Fin n → ℝ → ℝ) (L : ℝ)
    (hL : ∀ i, ∀ a b : ℝ, |φ i a - φ i b| ≤ L * |a - b|) (lam : ℝ) (hlam : 0 < lam)
    (γ : Fin n → ℝ) (hγ : ∀ i, 0 ≤ γ i) (α αstar : Fin n → ℝ) (hα : Feasible φ α)
    (hstar : Feasible φ αstar) (s : ℝ) (hs : 0 < s) :
    (1 / (n : ℝ)) * ∑ i, (‖x i‖ ^ 2 - γ i * lam * n / s) * (αstar i - α i) ^ 2 ≤
      4 * L ^ 2 * (countBelow γ (s / (lam * n)) : ℝ) / n := by sorry

end SDCA.AlmostSmooth
