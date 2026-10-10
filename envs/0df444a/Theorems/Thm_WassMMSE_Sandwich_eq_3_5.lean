-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_eq_3_5
-- name    : WassMMSE.Sandwich.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:29.402439+00:00
-- url     : https://prove2.me/theorems/660cfea4-17d7-4244-8492-610a8f3ca3a5
-- title:
--   (3.5), proof of Theorem 3.5, p. 13 — over normal priors, restricting 𝓕 to affine estimators 𝓐 does not change the maximin value
-- statement:
--   Let the nominal distribution be normal of the form (3.2), $\widehat{\mathbb P}=\mathcal N(\widehat\mu_x,\widehat\Sigma_x)\times\mathcal N(\widehat\mu_w,\widehat\Sigma_w)$ with $\widehat\Sigma_x\succeq0$, $\widehat\Sigma_w\succeq0$, and let $\rho_x,\rho_w\ge0$. Then, in the dual Wasserstein MMSE estimation problem with normal priors, the family $\mathcal F$ of all estimators may be restricted to the family $\mathcal A$ of affine estimators without changing the optimal value:
--   $$\sup_{\mathbb Q\in\mathbb B_{\mathcal N}(\widehat{\mathbb P})}\ \inf_{\psi\in\mathcal F}\ \mathcal R(\psi,\mathbb Q)=\sup_{\mathbb Q\in\mathbb B_{\mathcal N}(\widehat{\mathbb P})}\ \inf_{\psi\in\mathcal A}\ \mathcal R(\psi,\mathbb Q).\tag{3.5}$$
--
--   This is the first step of the proof of Theorem 3.5: under a normal prior the Bayesian MMSE estimator is affine, so the dual problem over normal priors becomes a problem about first and second moments only.
--
--   **Formalization Note** Both sides lie in $[0,\infty]$. No positive definiteness of $\widehat\Sigma_w$ is assumed, as on the page.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 13, (3.5), proof of Theorem 3.5

import Mathlib
import Definitions.Def_WassMMSE_Sandwich_Setting

open MeasureTheory ProbabilityTheory

namespace WassMMSE.Sandwich

/-- (3.5), proof of Theorem 3.5 (arXiv:1911.03539v2, p. 13). For a normal nominal distribution of
the form (3.2), in the dual problem over normal priors the family `𝓕` of all estimators may be
restricted to the affine estimators `𝓐` without changing the optimal value:
`sup_{ℚ ∈ 𝔹_𝒩(ℙ̂)} inf_{ψ ∈ 𝓕} 𝓡(ψ, ℚ) = sup_{ℚ ∈ 𝔹_𝒩(ℙ̂)} inf_{ψ ∈ 𝓐} 𝓡(ψ, ℚ)`. -/
theorem eq_3_5 {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ) (hρx : 0 ≤ ρx)
    (hρw : 0 ≤ ρw) (μx : E n) (Shx : Matrix (Fin n) (Fin n) ℝ) (hShx : Shx.PosSemidef)
    (μw : E m) (Shw : Matrix (Fin m) (Fin m) ℝ) (hShw : Shw.PosSemidef) :
    normalMaximin H ρx ρw μx Shx μw Shw =
      ⨆ (Q : Measure (E n × E m)) (_ : Q ∈ normalSet ρx ρw μx Shx μw Shw),
        ⨅ (ψ : E m → E n) (_ : IsAffineEstimator ψ), risk H ψ Q := by sorry

end WassMMSE.Sandwich
