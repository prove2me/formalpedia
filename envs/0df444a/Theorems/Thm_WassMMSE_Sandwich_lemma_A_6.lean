-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_lemma_A_6
-- name    : WassMMSE.Sandwich.lemma_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:25.965663+00:00
-- url     : https://prove2.me/theorems/ce4d9696-1b4c-4b7c-baac-6c053f93e34f
-- title:
--   Lemma A.6, p. 41 — the covariance Gelbrich set 𝒮 is convex and compact, with Tr[Σ] ≤ (ρ + Tr[Σ̂]^{1/2})²
-- statement:
--   Let $\widehat\Sigma\in\mathbb S^d_+$ and $\rho\ge0$. Then the set
--   $$\mathcal S=\Big\{\Sigma\in\mathbb S^d_+:\ \operatorname{Tr}\big[\Sigma+\widehat\Sigma-2(\widehat\Sigma^{1/2}\Sigma\widehat\Sigma^{1/2})^{1/2}\big]\le\rho^2\Big\}$$
--   is convex and compact, and every $\Sigma\in\mathcal S$ satisfies
--   $$\operatorname{Tr}[\Sigma]\le\big(\rho+\operatorname{Tr}[\widehat\Sigma]^{1/2}\big)^2.$$
--
--   The lemma supplies the compactness on which the existence of worst-case covariance matrices and the minimax interchanges of the paper rest.
--
--   **Formalization Note** Compactness is in $\mathbb R^{d\times d}$ with its standard (finite-dimensional) topology. $\mathcal S$ is the mission's `covGelbrichSet`.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 41, Lemma A.6

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassMMSE_Sandwich_Programs

open Matrix Topology WassersteinDRO.Gelbrich

namespace WassMMSE.Sandwich

/-- Lemma A.6 (arXiv:1911.03539v2, p. 41): for `Σ̂ ∈ 𝕊^d_+` and `ρ ≥ 0` the set
`𝒮 = {Σ ∈ 𝕊^d_+ : Tr[Σ + Σ̂ − 2(Σ̂^{1/2} Σ Σ̂^{1/2})^{1/2}] ≤ ρ²}` is convex and compact, and every
`Σ ∈ 𝒮` has `Tr[Σ] ≤ (ρ + Tr[Σ̂]^{1/2})²`. -/
theorem lemma_A_6 {d : ℕ} (Sh : Matrix (Fin d) (Fin d) ℝ) (hSh : Sh.PosSemidef) (ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    Convex ℝ (covGelbrichSet ρ Sh) ∧ IsCompact (covGelbrichSet ρ Sh) ∧
      ∀ S ∈ covGelbrichSet ρ Sh, S.trace ≤ (ρ + Real.sqrt Sh.trace) ^ 2 := by sorry

end WassMMSE.Sandwich
