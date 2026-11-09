-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_B_2
-- name    : SpatialHalfspace.FullLabels.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:20.491526+00:00
-- url     : https://prove2.me/theorems/d5451f43-b34c-40f2-abb1-0e0d62398e3f
-- title:
--   Lemma B.2 — Stability of risk minimization
-- statement:
--   Let $D\ge 2$, $P\in\mathcal E(\mu_D)$ and $\tau>0$. Suppose the estimates $\tilde\eta_{e,x}\in[0,1]$ satisfy $|\tilde\eta_{e,x}-\eta_{e,x}|\le\tau$ for every $e\in[q]$ and $x\in\{a_e,z_{e,0},z_{e,1}\}$. Define $\tilde R_e$ by replacing each $\eta_{e,x}$ with $\tilde\eta_{e,x}$ in (27), and for each $e$ choose a pattern $\hat b_e$ minimizing $\tilde R_e$ over $\mathcal P$. These patterns are simultaneously realizable by a halfspace, and every halfspace $\hat h\in H_D$ realizing them satisfies
--
--   $$R_{\bar P}(\hat h)-R^*_{\bar P}(H_D)\ \le\ 2(\alpha+2\rho)\tau .$$
--
--   This is the deterministic core of the proper upper bound.
--
--   Differences from the source:
--
--   - encoding: pairs e ∈ [q] with z_{e,0} = e_{2e−1}, z_{e,1} = e_{2e}, labels and indicators in {0,1} → e : Fin q (0-based) with basis indices 2e, 2e+1; labels and predictions in Bool, converted to 0/1 reals by bitR; reason: reindexing and identification only
--   - encoding: for each e choose a pattern b̂_e minimizing R̃_e over 𝒫 → for every family (b̂_e) with b̂_e ∈ 𝒫 and R̃_e(b̂_e) ≤ R̃_e(b) for all b ∈ 𝒫; reason: the conclusion holds for every such choice
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 16, PDF p. 17, Lemma B.2, PDF p. 17

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma B.2 (Stability of risk minimization), printed p. 16. Let `τ > 0` and estimates
`η̃_{e,x} ∈ [0,1]` with `|η̃_{e,x} − η_{e,x}| ≤ τ` at `x ∈ {a_e, z_{e,0}, z_{e,1}}`; let `R̃_e` be (27)
with `η̃`, and for each `e` let `b̂_e` minimize `R̃_e` over `𝒫`. These patterns are simultaneously
realizable by a halfspace, and every `ĥ ∈ H_D` realizing them has `R_P(ĥ) − R*_P(H_D) ≤ 2(α + 2ρ)τ`. -/
theorem lemma_B_2 (D : ℕ) (hD : 2 ≤ D) (P : Term D → Measure (Example D)) (hP : P ∈ env (muD D))
    (τ : ℝ) (hτ : 0 < τ) (ηt : Fin (D / 2) → Fin 3 → ℝ) (hηt : ∀ e j, 0 ≤ ηt e j ∧ ηt e j ≤ 1)
    (hclose : ∀ e j, |ηt e j - pairEta P e j| ≤ τ) (bhat : Fin (D / 2) → Bool × Bool × Bool)
    (hbhat : ∀ e, bhat e ∈ feasiblePatterns ∧
      ∀ b ∈ feasiblePatterns, pairRisk (ηt e) (bhat e) ≤ pairRisk (ηt e) b) :
    (∃ h ∈ homHalfspaces D, ∀ e, pattern h e = bhat e) ∧
    ∀ h ∈ homHalfspaces D, (∀ e, pattern h e = bhat e) →
      risk (mixture P) h - optRisk (mixture P) ≤ 2 * (alpha + 2 * rho) * τ := by sorry

end SpatialHalfspace.FullLabels
