-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_3_3
-- name    : SpatialHalfspace.FullLabels.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:59.445194+00:00
-- url     : https://prove2.me/theorems/0fe7363d-f95c-405d-892b-74239978a520
-- title:
--   Lemma 3.3 — Pairwise decomposition and halfspace realizability
-- statement:
--   Let $D\ge 2$, $q=\lfloor D/2\rfloor$, and let $Q^{(e)}_{s,t}$ be the midpoint switch on the coordinate pair $(z_{e,0},z_{e,1})$. Then for every $\sigma\in\{0,1\}^U$,
--
--   $$\bar P^\sigma=\frac1q\sum_{e\in[q]}Q^{(e)}_{\sigma_{(e,0)},\sigma_{(e,1)}}.\tag{19}$$
--
--   For every pair $e$ and every $h\in H_D$, the pattern $(h(a_e),h(z_{e,0}),h(z_{e,1}))$ lies in $\mathcal P=\{000,110,010,101,001,111\}$. Conversely, for any choice of patterns $p_e\in\mathcal P$, $e\in[q]$, a single halfspace $h\in H_D$ realizes $p_e$ on every pair $e$. Consequently, for every $\sigma$ there is $h\in H_D$ with
--
--   $$R_{Q^{(e)}_{\sigma_{(e,0)},\sigma_{(e,1)}}}(h)=R^*_{Q^{(e)}_{\sigma_{(e,0)},\sigma_{(e,1)}}}(H_D)\qquad\text{for every } e\in[q].$$
--
--   This decouples the pairs: halfspace optimization on $\bar P^\sigma$ splits into independent two-dimensional problems.
--
--   Differences from the source:
--
--   - encoding: pairs e ∈ [q] with z_{e,0} = e_{2e−1}, z_{e,1} = e_{2e}, labels and indicators in {0,1} → e : Fin q (0-based) with basis indices 2e, 2e+1; labels and predictions in Bool, converted to 0/1 reals by bitR; reason: reindexing and identification only
--   - encoding: attains the optimal halfspace risk on every terminal pair → the risk under the pair switch Q^{(e)} equals the infimum over all of H_D of risks under Q^{(e)}; reason: this is the meaning of the pairwise optimal risk in the proof of Theorem 3.4
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 8, PDF p. 9, Lemma 3.3, eq. (19), PDF p. 9 (proof in App. A.3, PDF p. 15)

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma 3.3 (Pairwise decomposition and halfspace realizability), printed p. 8. (19)
`P̄^σ = (1/q) ∑_e Q^{(e)}_{σ_(e,0), σ_(e,1)}`; every `h ∈ H_D` has a feasible pattern on every
pair; conversely any choice of feasible patterns `p_e` is realized by a single `h ∈ H_D`; hence for
every `σ` some `h ∈ H_D` attains the optimal halfspace risk on every terminal pair. -/
theorem lemma_3_3 (D : ℕ) (hD : 2 ≤ D) :
    (∀ σ : Term D → Bool, mixture (PM D σ) =
        (((D / 2 : ℕ) : ℝ≥0∞)⁻¹) • ∑ e : Fin (D / 2), pairSwitch e (σ (e, false)) (σ (e, true))) ∧
    (∀ e : Fin (D / 2), ∀ h ∈ homHalfspaces D, pattern h e ∈ feasiblePatterns) ∧
    (∀ pe : Fin (D / 2) → Bool × Bool × Bool, (∀ e, pe e ∈ feasiblePatterns) →
      ∃ h ∈ homHalfspaces D, ∀ e, pattern h e = pe e) ∧
    ∀ σ : Term D → Bool, ∃ h ∈ homHalfspaces D, ∀ e : Fin (D / 2),
      risk (pairSwitch e (σ (e, false)) (σ (e, true))) h =
        optRisk (pairSwitch e (σ (e, false)) (σ (e, true))) := by sorry

end SpatialHalfspace.FullLabels
