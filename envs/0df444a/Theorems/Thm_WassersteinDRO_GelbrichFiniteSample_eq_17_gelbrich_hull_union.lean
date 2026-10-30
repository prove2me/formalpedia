-- Prove2me | Theorems.Thm_WassersteinDRO_GelbrichFiniteSample_eq_17_gelbrich_hull_union
-- name    : WassersteinDRO.GelbrichFiniteSample.eq_17_gelbrich_hull_union
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:00:39.038997+00:00
-- url     : https://prove2.me/theorems/2a679e06-98fc-4c84-987f-1fb4f3cf5686
-- title:
--   Eq. (17): $\mathbb G_\varepsilon(\widehat\mu, \widehat\Sigma) = \bigcup_{(\mu,\Sigma) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)} \mathcal P(\Xi, \mu, \Sigma)$
-- statement:
--   Let $\Xi \subseteq \mathbb R^m$, $\varepsilon \in \mathbb R$, $\widehat\mu \in \mathbb R^m$, and let $\widehat\Sigma$ be a symmetric positive semidefinite $m \times m$ matrix. Then the Gelbrich hull is the union of the Chebyshev ambiguity sets over the uncertainty set:
--
--   $$\mathbb G_\varepsilon(\widehat\mu, \widehat\Sigma) = \bigcup_{(\mu, \Sigma) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)} \mathcal P(\Xi, \mu, \Sigma).$$
--
--   Consequently, if the Gelbrich hull contains a distribution, it contains every distribution on $\Xi$ with the same mean vector and covariance matrix. This representation is how the Gelbrich hull is related to moment information, and it is the step of Theorem 22 that places the true distribution in the hull once its moments lie in the uncertainty set.
--
--   **Formalization Note** Both inclusions are asserted. $\widehat\Sigma \in \mathbb S^m_+$ is the standing assumption of §2.3.
--
--   Differences from the source:
--   - generalization: Ξ ⊆ R^m closed (p. 6), radius ε ≥ 0 → any set Ξ ⊆ ℝ^m and any real ε; reason: the identity holds for every Ξ and ε, and specializes to the paper's closed Ξ and ε ≥ 0.
--   - encoding: P(Ξ), distributions supported on Ξ → probability measures Q with Q(Ξᶜ) = 0; reason: the standard meaning of "supported on Ξ" for a closed Ξ.
--   - encoding: distributions with mean vector µ and covariance matrix Σ → HasMeanCov, which includes finite second moments; reason: having a covariance matrix presupposes finite second moments.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.3, eq. (17), p. 18

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_chebyshevSet
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichHull
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **Eq. (17): the Gelbrich hull is a union of Chebyshev ambiguity sets.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.3, eq. (17), p. 18: "If we define P(Ξ, µ, Σ) as the Chebyshev ambiguity set that contains
all distributions on Ξ with mean vector µ and covariance matrix Σ, then the Gelbrich hull can also
be expressed as G_ε(µ̂, Σ̂) = ⋃_{(µ,Σ)∈U_ε(µ̂,Σ̂)} P(Ξ, µ, Σ). (17)"

For every `Ξ ⊆ ℝ^m`, `ε ∈ ℝ`, `µ̂ ∈ ℝ^m` and positive semidefinite `Σ̂`,
`G_ε(µ̂, Σ̂) = ⋃_{(µ, Σ) ∈ U_ε(µ̂, Σ̂)} P(Ξ, µ, Σ)` (both inclusions).

**Formalization Note.** `Σ̂ ∈ S^m_+` is the standing assumption of §2.3 (p. 16: "we assume
throughout this section that P̂_N has mean vector µ̂ ∈ R^m and covariance matrix Σ̂ ∈ S^m_+").
The closedness of `Ξ` (p. 6) is not needed for this identity and is not assumed, so the statement
covers the paper's closed `Ξ`. -/
theorem eq_17_gelbrich_hull_union {m : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (μh : EuclideanSpace ℝ (Fin m)) (Sigh : Matrix (Fin m) (Fin m) ℝ) (hSigh : Sigh.PosSemidef) :
    gelbrichHull Ξ ε μh Sigh = ⋃ p ∈ uncertaintySet ε μh Sigh, chebyshevSet Ξ p.1 p.2 := by sorry

end WassersteinDRO.GelbrichFiniteSample
