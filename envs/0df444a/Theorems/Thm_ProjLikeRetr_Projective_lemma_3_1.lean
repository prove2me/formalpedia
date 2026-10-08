-- Prove2me | Theorems.Thm_ProjLikeRetr_Projective_lemma_3_1
-- name    : ProjLikeRetr.Projective.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:38:37.811416+00:00
-- url     : https://prove2.me/theorems/552c6f76-d1ce-4f3e-be13-df7e762121a5
-- title:
--   Lemma 3.1, p. 7 — the projection onto a C^k manifold is locally single-valued, C^(k−1), with DP_M(x̄) = P_{T_M(x̄)}
-- statement:
--   Let $\mathcal M$ be a submanifold of the Euclidean space $\mathcal E$ of class $C^k$ ($k\ge2$) and dimension $d$ around $\bar x\in\mathcal M$, and let $P_{\mathcal M}(x)=\operatorname{argmin}\{\|x-y\|:y\in\mathcal M\}$ be the (set-valued) projection onto $\mathcal M$. Then $P_{\mathcal M}$ is a well-defined function around $\bar x$: there are $\delta>0$ and a map $P:\mathcal E\to\mathcal E$ such that, for every $x$ in the open ball $B(\bar x,\delta)$,
--
--   $$P_{\mathcal M}(x)=\{P(x)\},$$
--
--   so the nearest point of $\mathcal M$ to $x$ exists and is unique. Moreover $P$ is of class $C^{k-1}$ on $B(\bar x,\delta)$ and its derivative at $\bar x$ is the orthogonal projector onto the tangent space,
--
--   $$\mathrm DP_{\mathcal M}(\bar x)=P_{T_{\mathcal M}(\bar x)}.$$
--
--   No closedness or convexity of $\mathcal M$ is assumed. The lemma is the basis of the projective retraction (Proposition 3.2).
--
--   **Formalization Note** The projection set is $\{z: z\in\mathcal M,\ \|x-z\|\le\|x-w\|\ \forall w\in\mathcal M\}$ (the platform predicate `IsMetricProjection`). The set equality with a singleton asserts both existence and uniqueness. The derivative identity is claimed at $\bar x$ only, as on the page; $P_{T_{\mathcal M}(\bar x)}$ is `Submodule.starProjection`.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 7, Lemma 3.1

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Projective

/-- Lemma 3.1, p. 7 (Projection onto a manifold): if `M` is a `C^k` submanifold (`k ≥ 2`)
around `x̄ ∈ M`, then on some ball `B(x̄, δ)` the projection `P_M(x)` (the set of nearest points
of `M` to `x`) is a single point `P x`, the map `P` is `C^{k-1}` on that ball, and
`DP(x̄) = P_{T_M(x̄)}`, the orthogonal projector onto the tangent space. -/
theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ δ > 0, ∃ P : E → E,
      (∀ x ∈ Metric.ball xbar δ, {z | IsMetricProjection M x z} = {P x}) ∧
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball xbar δ) ∧
      HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M xbar).starProjection xbar := by sorry

end ProjLikeRetr.Projective
