-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_corollary22_robust_upper_bound
-- name    : RobustGeneralization.GaussUpper.corollary22_robust_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:28:35.260536+00:00
-- url     : https://prove2.me/theorems/7345478d-0478-4ba0-bb07-156ce6126dab
-- title:
--   Corollary 22 — f_ŵ has ℓ∞^ε-robust error ≤ 0.01 w.p. ≥ 1 − 2exp(−d/(8(σ²+1))) once n ≥ 1 (ε ≤ d^{−1/4}/4) or n ≥ 64ε²√d (d^{−1/4}/4 ≤ ε ≤ 1/4)
-- statement:
--   Let $(x_1,y_1),\dots,(x_n,y_n)\in\mathbb R^d\times\{\pm1\}$ be drawn i.i.d. from a $(\theta^\star,\sigma)$-Gaussian model with $\|\theta^\star\|_2=\sqrt d$ and $0<\sigma\le\frac1{32}d^{1/4}$. Let $\bar z=\frac1n\sum_{i=1}^ny_ix_i$ and let $\widehat w=\bar z/\|\bar z\|_2$ be the unit vector in its direction. Then with probability at least $1-2\exp\big(-\frac{d}{8(\sigma^2+1)}\big)$, the linear classifier $f_{\widehat w}$ has $\ell_\infty^\varepsilon$-robust classification error at most $0.01$ provided
--
--   $$n\ge\begin{cases}1 & \text{for }\varepsilon\le\frac14d^{-1/4},\\[2pt] 64\,\varepsilon^2\sqrt d & \text{for }\frac14d^{-1/4}\le\varepsilon\le\frac14.\end{cases}$$
--
--   This is the upper half of the paper's separation in the Gaussian model: a single sample suffices for small standard error, but $\ell_\infty$-robustness at level $\varepsilon$ is achieved by a simple estimator once $n$ grows like $\varepsilon^2\sqrt d$, which matches the paper's lower bound up to logarithmic factors.
--
--   **Formalization Note** The conclusion is a bound on the failure set: the samples on which the robust error exceeds $0.01$ have probability at most $2\exp(-d/(8(\sigma^2+1)))$. The two-case condition on $n$ is the disjunction of "$\varepsilon\le\frac14d^{-1/4}$ and $n\ge1$" and "$\frac14d^{-1/4}\le\varepsilon\le\frac14$ and $n\ge64\varepsilon^2\sqrt d$"; negative $\varepsilon$ falls in the first case. $d^{\pm1/4}$ is the real power; since $\sigma>0$, the hypothesis on $\sigma$ forces $d\ge1$. The $\ell_\infty$ ball is coordinatewise, and the classifier breaks ties towards $+1$.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 27, Corollary 22

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Corollary 22** (p. 27). For `n` i.i.d. samples of the `(θ⋆, σ)`-Gaussian model with
`‖θ⋆‖₂ = √d` and `σ ≤ d^{1/4}/32`, and `ŵ = z̄/‖z̄‖₂`, `z̄ = (1/n) ∑ yᵢ xᵢ`: with probability at least
`1 - 2 exp(-d/(8(σ² + 1)))` the classifier `f_ŵ` has ℓ∞^ε-robust classification error at most
`0.01` if `n ≥ 1` for `ε ≤ d^{-1/4}/4` and `n ≥ 64 ε² √d` for `d^{-1/4}/4 ≤ ε ≤ 1/4`.
Stated as a bound on the failure set. -/
theorem corollary22_robust_upper_bound (d n : ℕ) (θ : E d) (hθ : ‖θ‖ = Real.sqrt d) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ ≤ (1 / 32) * (d : ℝ) ^ ((1 : ℝ) / 4)) (ε : ℝ)
    (hn : (ε ≤ (1 / 4) * (d : ℝ) ^ (-(1 : ℝ) / 4) ∧ 1 ≤ n) ∨
      ((1 / 4) * (d : ℝ) ^ (-(1 : ℝ) / 4) ≤ ε ∧ ε ≤ 1 / 4 ∧
        64 * ε ^ 2 * Real.sqrt d ≤ n)) :
    (Measure.pi fun _ : Fin n => gaussModel θ σ)
        {S | ENNReal.ofReal (1 / 100) < robustErr (gaussModel θ σ) (linClf (what S)) ε} ≤
      ENNReal.ofReal (2 * Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by sorry

end RobustGeneralization.GaussUpper
