-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_D_1
-- name    : SpatialHalfspace.FullLabels.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:19.156197+00:00
-- url     : https://prove2.me/theorems/06934575-e18e-4f09-b0fc-713da7fae3df
-- title:
--   Lemma D.1 — Bayes predictions and excess risk
-- statement:
--   Let $D\ge 2$, $q=\lfloor D/2\rfloor$ and $\sigma\in\{0,1\}^q$. Under $\tilde P^\sigma$ (at terminal $(e,0)$ the nonzero support points have label probability $\sigma_e$, at $(e,1)$ they have $1/2$, the origin has label $0$), every nonzero support point of pair $e$ has conditional label probability $1/4+\sigma_e/2$ under the mixture. The Bayes classifier $x\mapsto 1\{\bar P(Y=1\mid X=x)>1/2\}$ predicts $\sigma_e$ at the three nonzero support points of each pair and $0$ at the origin. These predictions are realized by a homogeneous halfspace. Every measurable binary classifier $g$ satisfies
--
--   $$R_{\tilde P^\sigma}(g)-R^*_{\tilde P^\sigma}(H_D)\ \ge\ \frac{\rho}{2q}\sum_{e\in[q]}1\{g(z_{e,0})\ne\sigma_e\}.\tag{31}$$
--
--   This is the risk–recovery link for the improper lower bound: any good classifier, proper or not, reveals most bits $\sigma_e$.
--
--   Differences from the source:
--
--   - encoding: pairs e ∈ [q] with z_{e,0} = e_{2e−1}, z_{e,1} = e_{2e}, labels and indicators in {0,1} → e : Fin q (0-based) with basis indices 2e, 2e+1; labels and predictions in Bool, converted to 0/1 reals by bitR; reason: reindexing and identification only
--   - reading: the Bayes classifier predicts σ_e at the three nonzero support points and zero at the origin → the classifier 1{P̄(Y=1|X=x) > 1/2} evaluated at these four points; reason: this is the Bayes classifier; there are no ties at these points
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 19, PDF p. 20, Lemma D.1, eq. (31), PDF p. 20

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma D.1 (Bayes predictions and excess risk), printed p. 19. Under `P̃^σ`, every nonzero
support point of pair `e` has conditional label probability `1/4 + σ_e/2`; the Bayes classifier
`1{P̄(Y=1|X=x) > 1/2}` predicts `σ_e` at the three nonzero support points of each pair and `0` at
the origin; these predictions are realized by a homogeneous halfspace; and every measurable binary
classifier `g` satisfies (31) `R(g) − R*(H_D) ≥ (ρ/(2q)) ∑_e 1{g(z_{e,0}) ≠ σ_e}`. -/
theorem lemma_D_1 (D : ℕ) (hD : 2 ≤ D) (σ : Fin (D / 2) → Bool) :
    (∀ e j, condProbOne (mixture (PT D σ)) (pairPoint e j) = 1 / 4 + bitR (σ e) / 2) ∧
    (∀ e j, decide (1 / 2 < condProbOne (mixture (PT D σ)) (pairPoint e j)) = σ e) ∧
    decide (1 / 2 < condProbOne (mixture (PT D σ)) 0) = false ∧
    (∃ h ∈ homHalfspaces D, (∀ e j, h (pairPoint e j) = σ e) ∧ h 0 = false) ∧
    ∀ g : Vec D → Bool, Measurable g →
      rho / (2 * ((D / 2 : ℕ) : ℝ)) * ∑ e : Fin (D / 2), bitR (decide (g (zpt e false) ≠ σ e)) ≤
        risk (mixture (PT D σ)) g - optRisk (mixture (PT D σ)) := by sorry

end SpatialHalfspace.FullLabels
