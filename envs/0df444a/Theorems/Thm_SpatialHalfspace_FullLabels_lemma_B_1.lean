-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_B_1
-- name    : SpatialHalfspace.FullLabels.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:54.71422+00:00
-- url     : https://prove2.me/theorems/7c543e36-0050-403e-a4ff-86ddb9f82543
-- title:
--   Lemma B.1 — Risk decomposition and minimization
-- statement:
--   Let $D\ge 2$, $q=\lfloor D/2\rfloor$, and $P\in\mathcal E(\mu_D)$. With $\eta_{e,x}=(\eta_{(e,0),x}+\eta_{(e,1),x})/2$, $\ell(b,t)=t+b(1-2t)$, $R_e(A,B_0,B_1)=\alpha\ell(A,\eta_{e,a_e})+\rho\ell(B_0,\eta_{e,z_{e,0}})+\rho\ell(B_1,\eta_{e,z_{e,1}})$, $C_0(P)=\zeta\,\bar P(Y=1\mid X=0)$ and $b_e(h)=(h(a_e),h(z_{e,0}),h(z_{e,1}))$: every $h\in H_D$ satisfies
--
--   $$R_{\bar P}(h)=C_0(P)+\frac1q\sum_{e\in[q]}R_e(b_e(h)),\tag{28}$$
--
--   and
--
--   $$R^*_{\bar P}(H_D)=C_0(P)+\frac1q\sum_{e\in[q]}\min_{b\in\mathcal P}R_e(b).\tag{29}$$
--
--   The origin's label is arbitrary in $\mathcal E(\mu_D)$; its contribution $C_0(P)$ is common to all halfspaces because every halfspace predicts $0$ at the origin.
--
--   Differences from the source:
--
--   - encoding: pairs e ∈ [q] with z_{e,0} = e_{2e−1}, z_{e,1} = e_{2e}, labels and indicators in {0,1} → e : Fin q (0-based) with basis indices 2e, 2e+1; labels and predictions in Bool, converted to 0/1 reals by bitR; reason: reindexing and identification only
--   - encoding: η_{u,x} = P_u(Y = 1 | X = x), min over 𝒫 → the ratio P_u{(x,1)}/P_u({x} × {0,1}) at atoms (condProbOne), and Finset.inf’ over the nonempty finite set 𝒫; reason: the support points have positive mass, so the ratio is the conditional probability
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 15, PDF p. 16, Lemma B.1, eqs. (26)–(29), PDF p. 16

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma B.1 (Risk decomposition and minimization), printed p. 15. For `P ∈ E(μ_D)`, every
`h ∈ H_D` satisfies (28) `R_P(h) = C₀(P) + (1/q) ∑_e R_e(b_e(h))`, and (29)
`R*_P(H_D) = C₀(P) + (1/q) ∑_e min_{b ∈ 𝒫} R_e(b)`. -/
theorem lemma_B_1 (D : ℕ) (hD : 2 ≤ D) (P : Term D → Measure (Example D)) (hP : P ∈ env (muD D)) :
    (∀ h ∈ homHalfspaces D, risk (mixture P) h =
        originRisk P + (((D / 2 : ℕ) : ℝ))⁻¹ * ∑ e : Fin (D / 2), pairRisk (pairEta P e) (pattern h e)) ∧
    optRisk (mixture P) =
      originRisk P + (((D / 2 : ℕ) : ℝ))⁻¹ * ∑ e : Fin (D / 2), minPairRisk (pairEta P e) := by sorry

end SpatialHalfspace.FullLabels
