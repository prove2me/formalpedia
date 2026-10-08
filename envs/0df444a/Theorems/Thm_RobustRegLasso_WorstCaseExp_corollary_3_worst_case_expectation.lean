-- Prove2me | Theorems.Thm_RobustRegLasso_WorstCaseExp_corollary_3_worst_case_expectation
-- name    : RobustRegLasso.WorstCaseExp.corollary_3_worst_case_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:50.458992+00:00
-- url     : https://prove2.me/theorems/86f9d52b-b0ef-4299-9f32-5f88e1e49e49
-- title:
--   Corollary 3 — $\|b-Ax\|_2+\sqrt n c\|x\|_1+\sqrt n c=\sup_{\mu\in\hat{\mathcal P}(n)}\sqrt{n\int(b'-r'^\top x)^2\,d\mu}$
-- statement:
--   Let $n\ge1$ and $m$ be integers, $b\in\mathbb R^n$, $A=(a_{ij})\in\mathbb R^{n\times m}$ with rows $r_i^\top$, and $c\ge0$. For $\sigma\in\mathbb R^n$ and $\Delta=(\delta_{ij})\in\mathbb R^{n\times m}$ with columns $\delta_1,\dots,\delta_m$, let $\mathcal Z_i=[b_i-\sigma_i,b_i+\sigma_i]\times\prod_{j=1}^m[a_{ij}-\delta_{ij},a_{ij}+\delta_{ij}]$ and let
--   $$\mathcal P_n(A,\Delta,b,\sigma)=\Big\{\mu \text{ Borel probability measure on }\mathbb R^{m+1}\ \Big|\ \forall S\subseteq\{1,\dots,n\}:\ \mu\Big(\bigcup_{i\in S}\mathcal Z_i\Big)\ge\frac{|S|}{n}\Big\},\qquad
--   \hat{\mathcal P}(n)=\bigcup_{\|\sigma\|_2\le\sqrt n c;\ \forall j:\ \|\delta_j\|_2\le\sqrt n c}\mathcal P_n(A,\Delta,b,\sigma).$$
--   Then for every $x\in\mathbb R^m$,
--   $$\|b-Ax\|_2+\sqrt n\,c\,\|x\|_1+\sqrt n\,c=\sup_{\mu\in\hat{\mathcal P}(n)}\sqrt{\,n\int_{\mathbb R^{m+1}}(b'-r'^\top x)^2\,d\mu(r',b')\,}.$$
--
--   The equation is deterministic: it holds for an arbitrary data set $(b,A)$, with no probabilistic assumption on how the samples were generated. It says that the robust (equivalently, $\ell_1$-regularized) regression loss on the training data equals the worst-case expected squared prediction error, over a class of distributions placing mass at least $|S|/n$ on the union of the boxes around any $|S|$ samples. This is the bridge the paper uses to derive the consistency of Lasso from robustness.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$ and stated as a least upper bound (`IsLUB`); the paper does not claim it is attained and the statement does not either. The integral is the Lebesgue integral of the nonnegative integrand in $[0,\infty]$ (no Bochner integral, no integrability hypothesis), and the left-hand side, a nonnegative real, is embedded in $[0,\infty]$. Points of $\mathbb R^{m+1}$ are `Fin (m+1) → ℝ` with the response first. The hypotheses $n\ge1$ and $c\ge0$ are the paper's setting, implicit on the page; $c$ is a fixed constant (the paper's $c_n$). No sign condition is imposed on $\sigma$ or $\Delta$, exactly as printed: a pair with some negative entry gives an empty box $\mathcal Z_i$, and then $\mathcal P_n(A,\Delta,b,\sigma)=\emptyset$ (take $S=\{i\}$), so such pairs add nothing to $\hat{\mathcal P}(n)$.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 11, Corollary 3, Eq. (8) (restated with proof on p. 22, Appendix D, Eq. (20))

import Mathlib
import Definitions.Def_RobustRegLasso_WorstCaseExp_Basic

namespace RobustRegLasso.WorstCaseExp

/-- Corollary 3, Eq. (8) (arXiv:0811.1790v1, p. 11; restated as Eq. (20), p. 22): for every
`b ∈ ℝⁿ` (`n ≥ 1`), `A ∈ ℝ^{n×m}`, `c ≥ 0` and `x ∈ ℝᵐ`,
`‖b − Ax‖₂ + √n c‖x‖₁ + √n c = sup_{μ ∈ P̂(n)} √(n ∫_{ℝ^{m+1}} (b' − r'ᵀx)² dμ(r', b'))`,
the supremum taken in `[0, ∞]` as a least upper bound. -/
theorem corollary_3_worst_case_expectation {n m : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (x : Fin m → ℝ) :
    IsLUB {v : ENNReal | ∃ μ ∈ hatP A b c, v = rootScaledRisk n x μ}
      (ENNReal.ofReal (regularizedLoss A b c x)) := by sorry

end RobustRegLasso.WorstCaseExp
