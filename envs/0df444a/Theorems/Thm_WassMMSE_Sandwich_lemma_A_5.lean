-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_lemma_A_5
-- name    : WassMMSE.Sandwich.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:15.095109+00:00
-- url     : https://prove2.me/theorems/8fa0ec5a-9f7d-4188-b00e-9fc516ce7de1
-- title:
--   Lemma A.5, p. 40 — the nonlinear SDP (A.9) has a maximizer Σ⋆ ⪰ λ_min(Σ̂) I_d
-- statement:
--   Let $\widehat\Sigma\in\mathbb S^d_+$ and $\rho\ge0$, let $\mathcal C\subseteq\mathbb R^{\ell\times d}$ be non-empty and convex, and let $f:\mathcal C\to\mathbb R$ be convex and continuous on $\mathcal C$. Consider the nonlinear semidefinite program (A.9)
--   $$\sup_{\Sigma\succeq0}\ \inf_{L\in\mathcal C}\ \langle L^\top L,\Sigma\rangle+f(L)\quad\text{s.t.}\quad\operatorname{Tr}\big[\Sigma+\widehat\Sigma-2(\widehat\Sigma^{1/2}\Sigma\widehat\Sigma^{1/2})^{1/2}\big]\le\rho^2.$$
--   Then (A.9) admits a maximizer $\Sigma^\star$ with $\Sigma^\star\succeq\lambda_{\min}(\widehat\Sigma)I_d$: $\Sigma^\star$ is feasible, $\Sigma^\star-\lambda_{\min}(\widehat\Sigma)I_d$ is positive semidefinite, and the objective value at $\Sigma^\star$ equals the supremum of (A.9).
--
--   This structural property lets the dual estimation problem be restricted to covariance matrices bounded away from zero, which is how the normal noise covariance is kept positive definite in the proof of Theorem 3.5.
--
--   **Formalization Note** The inner infimum can be $-\infty$ when $\mathcal C$ is unbounded, so the objective is computed in `EReal`. $\lambda_{\min}$ is the mission's `lamMin` ($0$ at $d=0$, where the bound is vacuous).
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 40, (A.9) and Lemma A.5

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassMMSE_Sandwich_Programs

open Matrix Topology WassersteinDRO.Gelbrich

namespace WassMMSE.Sandwich

/-- Lemma A.5 (arXiv:1911.03539v2, p. 40): for `Σ̂ ∈ 𝕊^d_+`, `ρ ≥ 0`, a non-empty convex
`𝒞 ⊆ ℝ^{ℓ×d}` and a convex continuous `f : 𝒞 → ℝ`, the nonlinear SDP (A.9)
`sup_{Σ ∈ 𝒮} inf_{L ∈ 𝒞} ⟨LᵀL, Σ⟩ + f(L)` admits a maximizer `Σ⋆ ⪰ λ_min(Σ̂) I_d`. -/
theorem lemma_A_5 {d ℓ : ℕ} (Sh : Matrix (Fin d) (Fin d) ℝ) (hSh : Sh.PosSemidef) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (C : Set (Matrix (Fin ℓ) (Fin d) ℝ)) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : Matrix (Fin ℓ) (Fin d) ℝ → ℝ) (hf : ConvexOn ℝ C f) (hfc : ContinuousOn f C) :
    let g : Matrix (Fin d) (Fin d) ℝ → EReal := fun S =>
      ⨅ (L : Matrix (Fin ℓ) (Fin d) ℝ) (_ : L ∈ C), ((frob (Lᵀ * L) S + f L : ℝ) : EReal)
    ∃ Ss ∈ covGelbrichSet ρ Sh, (Ss - lamMin Sh • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
      g Ss = ⨆ (S : Matrix (Fin d) (Fin d) ℝ) (_ : S ∈ covGelbrichSet ρ Sh), g S := by sorry

end WassMMSE.Sandwich
