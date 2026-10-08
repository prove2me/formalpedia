-- Prove2me | Theorems.Thm_SAG_LargeStep_sg_one_step
-- name    : SAG.LargeStep.sg_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:15.08782+00:00
-- url     : https://prove2.me/theorems/4a22faeb-7e60-42c6-b963-96d7bde80cf1
-- title:
--   §A.3 — one stochastic gradient step: δ_k ≤ δ_{k−1} − 2γ_k(1 − γ_kL)E[g′(x̃^{k−1})ᵀ(x̃^{k−1} − x*)] + 2γ_k²σ²
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Let $\gamma_1,\gamma_2,\dots$ be any real step sizes, $\tilde x^0\in\mathbb R^p$, and let $\tilde x^j$ be the stochastic gradient iterates $\tilde x^j=\tilde x^{j-1}-\gamma_jf'_{i_j}(\tilde x^{j-1})$ with $i_1,i_2,\dots$ independent and uniform on $\{1,\dots,n\}$. Write $\delta_k=\mathbb E\|\tilde x^k-x^*\|^2$. Then for every $k\ge1$
--   $$\delta_k\le\delta_{k-1}-2\gamma_k(1-\gamma_kL)\,\mathbb E\big[g'(\tilde x^{k-1})^\top(\tilde x^{k-1}-x^*)\big]+2\gamma_k^2\sigma^2 .$$
--
--   This one-step recursion (following Bach and Moulines, 2011) is the basis of the bound on the averaged stochastic gradient iterate used to initialize SAG.
--
--   **Formalization Note** The statement is written for step $k+1$ ($k\ge0$). All expectations are uniform averages over $K\ge k+1$ indices (`SAGA.Convex.expectIdx n K`), the law of $K$ independent uniform draws.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 14, §A.3

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_sgRun

namespace SAG.LargeStep

/-- §A.3, p. 14: one stochastic gradient step in expectation, for any step sizes `γ`.
With `δ_k = E‖x̃ᵏ − x*‖²` (expectation over `K ≥ k + 1` i.i.d. uniform indices),
`δ_{k+1} ≤ δ_k − 2γ_{k+1}(1 − γ_{k+1}L) E[⟪g'(x̃ᵏ), x̃ᵏ − x*⟫] + 2γ_{k+1}²σ²`. -/
theorem sg_one_step {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (γ : ℕ → ℝ) (x0 : EuclideanSpace ℝ (Fin p)) {K : ℕ} (k : ℕ) (hk : k + 1 ≤ K) :
    SAGA.Convex.expectIdx n K (fun js => ‖sgIterate f' γ x0 js (k + 1) - xstar‖ ^ 2)
      ≤ SAGA.Convex.expectIdx n K (fun js => ‖sgIterate f' γ x0 js k - xstar‖ ^ 2)
        - 2 * γ (k + 1) * (1 - γ (k + 1) * L)
          * SAGA.Convex.expectIdx n K (fun js =>
              inner ℝ (SAGA.Convex.gradAvg f' (sgIterate f' γ x0 js k))
                (sgIterate f' γ x0 js k - xstar))
        + 2 * γ (k + 1) ^ 2 * sigmaSq f' xstar := by sorry

end SAG.LargeStep
