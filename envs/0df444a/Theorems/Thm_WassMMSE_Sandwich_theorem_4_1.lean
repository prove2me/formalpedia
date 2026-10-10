-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_theorem_4_1
-- name    : WassMMSE.Sandwich.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:33.51157+00:00
-- url     : https://prove2.me/theorems/acd94360-e7ac-4fef-8f3f-b05de36da7de
-- title:
--   Theorem 4.1, p. 16 — for a normal nominal distribution, the Gelbrich affine minimax value equals the maximin value over normal priors
-- statement:
--   Let $H\in\mathbb R^{m\times n}$, let the nominal distribution be normal of the form (3.2),
--   $$\widehat{\mathbb P}=\widehat{\mathbb P}_x\times\widehat{\mathbb P}_w,\qquad\widehat{\mathbb P}_x=\mathcal N(\widehat\mu_x,\widehat\Sigma_x),\quad\widehat{\mathbb P}_w=\mathcal N(\widehat\mu_w,\widehat\Sigma_w),$$
--   with $\widehat\Sigma_x\succeq0$ and $\widehat\Sigma_w\succ0$, and let $\rho_x,\rho_w\ge0$. Then the optimal values of the restricted primal and dual estimation problems (2.1) and (3.3) coincide:
--   $$\inf_{\psi\in\mathcal A}\ \sup_{\mathbb Q\in\mathbb G(\widehat{\mathbb P})}\ \mathcal R(\psi,\mathbb Q)=\sup_{\mathbb Q\in\mathbb B_{\mathcal N}(\widehat{\mathbb P})}\ \inf_{\psi\in\mathcal F}\ \mathcal R(\psi,\mathbb Q).$$
--
--   Since $\mathcal A\subseteq\mathcal F$ and $\mathbb B_{\mathcal N}(\widehat{\mathbb P})\subseteq\mathbb B(\widehat{\mathbb P})\subseteq\mathbb G(\widehat{\mathbb P})$, the two sides sandwich the Wasserstein MMSE problem (1.7) and its dual (3.1); the theorem therefore shows that all four values coincide, that an affine estimator is minimax-optimal and that a normal prior is least favourable.
--
--   **Formalization Note** Both sides are values in $[0,\infty]$. The hypothesis $\widehat\Sigma_w\succ0$ is added to the page's statement, which assumes only the form (3.2). It is necessary: for $n=m=1$, $H=0$, $\widehat\Sigma_x=1$, $\widehat\Sigma_w=0$ and $\rho_x=\rho_w=0$, the set $\mathbb B_{\mathcal N}(\widehat{\mathbb P})$ is empty (it requires $\Sigma_w>0$ with $\mathbb W(\mathcal N(0,\Sigma_w),\delta_0)=\sqrt{\Sigma_w}\le0$), so the right side is a supremum over the empty set, while the left side is $1$. The page's proof uses (3.8), which it derives only when $\widehat\Sigma_w\succ0$ (p. 14), and Corollaries 4.2 and 4.3, the theorem's applications, assume it. No positivity of $\rho_x,\rho_w$ is assumed.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 16, Theorem 4.1 (with the disclosed addition Σ̂_w ≻ 0)

import Mathlib
import Definitions.Def_WassMMSE_Sandwich_Setting

open MeasureTheory ProbabilityTheory

namespace WassMMSE.Sandwich

/-- Theorem 4.1 (Sandwich theorem; Nguyen et al., arXiv:1911.03539v2, p. 16). Let the nominal
distribution be normal of the form (3.2), `ℙ̂ = 𝒩(μ̂_x, Σ̂_x) × 𝒩(μ̂_w, Σ̂_w)`, with radii
`ρ_x, ρ_w ≥ 0`. Then the optimal value of the Gelbrich MMSE estimation problem (2.1),
`inf_{ψ ∈ 𝓐} sup_{ℚ ∈ 𝔾(ℙ̂)} 𝓡(ψ, ℚ)`, equals that of the dual problem over normal priors (3.3),
`sup_{ℚ ∈ 𝔹_𝒩(ℙ̂)} inf_{ψ ∈ 𝓕} 𝓡(ψ, ℚ)`.

The hypothesis `Σ̂_w ≻ 0` is a disclosed addition: the page states the theorem for `Σ̂_w ⪰ 0`, where
it fails (`n = m = 1`, `H = 0`, `Σ̂_x = 1`, `Σ̂_w = 0`, `ρ_x = ρ_w = 0`: `𝔹_𝒩(ℙ̂) = ∅`), and its proof
uses (3.8), established only for `Σ̂_w ≻ 0` (p. 14). -/
theorem theorem_4_1 {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ) (hρx : 0 ≤ ρx)
    (hρw : 0 ≤ ρw) (μx : E n) (Shx : Matrix (Fin n) (Fin n) ℝ) (hShx : Shx.PosSemidef)
    (μw : E m) (Shw : Matrix (Fin m) (Fin m) ℝ) (hShw : Shw.PosDef) :
    gelbrichMinimax H ρx ρw μx Shx μw Shw = normalMaximin H ρx ρw μx Shx μw Shw := by sorry

end WassMMSE.Sandwich
