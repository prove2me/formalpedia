-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_worstCaseExp_eq_covariance_sup
-- name    : WassInvCov.Shrinkage.worstCaseExp_eq_covariance_sup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:39.967952+00:00
-- url     : https://prove2.me/theorems/a8322b52-5412-41ee-8e05-38200dea1e9a
-- title:
--   Proof of Proposition 2.8, p. 8 — the worst case over the Gaussian ball 𝒫⁰_ρ is a supremum of ⟨S, X⟩ over the covariance ball 𝕎_S(S, Σ̂) ≤ ρ
-- statement:
--   Let $\rho>0$, let $\widehat\Sigma\in\mathbb S^p_+$ and $X\in\mathbb S^p_{++}$. Let $\mathcal P^0_\rho$ be the set of centred normal distributions on $\mathbb R^p$ within type-2 Wasserstein distance $\rho$ of $\mathcal N(0,\widehat\Sigma)$, and $g(\widehat\Sigma,X)=\sup_{\mathbb Q\in\mathcal P^0_\rho}\mathbb E^{\mathbb Q}[\langle\xi\xi^\top,X\rangle]$ the worst-case expectation (7). Then
--
--   $$g(\widehat\Sigma,X)=\sup_{S\in\mathbb S^p_+}\Big\{\langle S,X\rangle:\ \mathbb W_S(S,\widehat\Sigma)\le\rho\Big\},$$
--
--   where $\mathbb W_S$ is the metric of Definition 2.3.
--
--   This identity turns the worst case over distributions into a worst case over covariance matrices. It rests on two facts: the Wasserstein distance between two centred normal distributions is $\mathbb W_S$ of their covariances (the Gelbrich formula, Proposition 2.2, cited by the paper), and $\mathbb E^{\mathcal N(0,S)}[\xi\xi^\top]=S$. It is the first step of the proof of Proposition 2.8.
--
--   **Formalization Note** Both suprema are taken in the extended reals. The distance in $\mathcal P^0_\rho$ is the coupling Wasserstein distance (Definition 1.1), not $\mathbb W_S$; the identity is therefore not a matter of unfolding definitions.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 8, proof of Proposition 2.8, first display

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Proof of Proposition 2.8, p. 8, first display (arXiv:1805.07194v1): for `ρ > 0`, `Σ̂ ⪰ 0` and
`X ≻ 0`, the worst case of `𝔼^ℚ[⟨ξξᵀ, X⟩]` over the Gaussian Wasserstein ball `𝒫⁰_ρ` equals the
supremum of `⟨S, X⟩` over covariance matrices `S ⪰ 0` with `𝕎_S(S, Σ̂) ≤ ρ`. -/
theorem worstCaseExp_eq_covariance_sup {p : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (Sh X : Matrix (Fin p) (Fin p) ℝ) (hSh : Sh.PosSemidef) (hX : X.PosDef) :
    worstCaseExp ρ Sh X =
      ⨆ (S : Matrix (Fin p) (Fin p) ℝ) (_ : S.PosSemidef ∧ WS S Sh ≤ ρ),
        ((WassMMSE.Sandwich.frob S X : ℝ) : EReal) := by sorry

end WassInvCov.Shrinkage
