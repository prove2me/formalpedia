-- Prove2me | Theorems.Thm_RobustGeneralization_BernLower_theorem31_linear_robust_error_lower_bound
-- name    : RobustGeneralization.BernLower.theorem31_linear_robust_error_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:22:42.17615+00:00
-- url     : https://prove2.me/theorems/f04ab76c-280e-41dd-b53e-ff640347b402
-- title:
--   Theorem 31 — every linear learner has expected ℓ∞^ε-robust error ≥ ½ − γ when n ≤ ε²γ²/(5000 τ⁴ log(4d/γ))
-- statement:
--   Let $g_n$ be a linear-classifier learning algorithm, i.e. any function that maps $n$ samples from $\{-1,+1\}^d\times\{\pm1\}$ to a weight vector $w\in\mathbb R^d$. Choose $\theta^\star$ uniformly at random from $\{-1,+1\}^d$ and draw $n$ independent samples $S$ from the $(\theta^\star,\tau)$-Bernoulli model, where $0<\tau\le\tfrac14$; let $w=g_n(S)$. Let $0\le\varepsilon<3\tau$ and $0<\gamma<\tfrac12$. If
--   $$n\le\frac{\varepsilon^2\gamma^2}{5000\,\tau^4\log(4d/\gamma)},$$
--   then the linear classifier $f_w(x)=\operatorname{sgn}\langle w,x\rangle$ has expected $\ell_\infty^\varepsilon$-robust classification error at least $\tfrac12-\gamma$:
--   $$\mathbb E_{\theta^\star,S}\Big[\Pr_{(x,y)\sim P_{\theta^\star,\tau}}\big[\exists x'\in\mathcal B_\infty^\varepsilon(x):\ f_w(x')\ne y\big]\Big]\ge\frac12-\gamma.$$
--
--   With $\tau\asymp d^{-1/4}$ and constant $\varepsilon$ this says that linear classifiers need on the order of $\sqrt d$ samples (up to logarithmic factors) to be $\ell_\infty$-robust in the Bernoulli model, while a single sample suffices for standard accuracy; it is the explicit form of the paper's Theorem 9.
--
--   **Formalization Note** The learner sees only the samples, never $\theta^\star$, and the error is averaged over the uniform prior on $\theta^\star$. The tie $\langle w,x'\rangle=0$ is classified as $+1$. The hypothesis $\varepsilon\ge0$ is added: for $\varepsilon<0$ the ball is empty, the robust error is $0$, and the printed statement fails at $n=0$. At $d=0$, $\log 0=0$ in Lean makes the right-hand side of the sample bound $0$, forcing $n=0$, where the claim holds.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 35, Theorem 31

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem theorem31_linear_robust_error_lower_bound (d n : ℕ)
    (g : (Fin n → (Fin d → Bool) × Bool) → E d) (τ ε γ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) (hε : 0 ≤ ε) (hε' : ε < 3 * τ)
    (hγ : 0 < γ) (hγ' : γ < 1 / 2)
    (hn : (n : ℝ) ≤ ε ^ 2 * γ ^ 2 / (5000 * τ ^ 4 * Real.log (4 * d / γ))) :
    1 / 2 - γ ≤ expRobErr g τ ε := by sorry

end RobustGeneralization.BernLower
