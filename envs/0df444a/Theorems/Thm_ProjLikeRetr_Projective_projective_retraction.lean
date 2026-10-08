-- Prove2me | Theorems.Thm_ProjLikeRetr_Projective_projective_retraction
-- name    : ProjLikeRetr.Projective.projective_retraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:52:35.784239+00:00
-- url     : https://prove2.me/theorems/80850f38-5f59-4eb4-b6f3-eafb1fbca1ed
-- title:
--   Proposition 3.2, p. 8 — the projective retraction R(x, u) = P_M(x + u)
-- statement:
--   Let $\mathcal M$ be a submanifold of the Euclidean space $\mathcal E$ of class $C^k$ ($k\ge2$) and dimension $d$ around $\bar x\in\mathcal M$, and let $P_{\mathcal M}$ be the set-valued projection onto $\mathcal M$. Consider
--
--   $$R:\ T\mathcal M\to\mathcal M,\qquad (x,u)\mapsto P_{\mathcal M}(x+u).$$
--
--   Then $R$ is a retraction around $\bar x$: there is a map $r:\mathcal E\times\mathcal E\to\mathcal E$ such that
--
--   1. for all $(x,u)\in T\mathcal M$ close enough to $(\bar x,0)$, $P_{\mathcal M}(x+u)=\{r(x,u)\}$ (the projection of $x+u$ exists and is unique);
--   2. $r$ is a retraction on $\mathcal M$ around $\bar x$ in the sense of Definition 2.1: on a neighbourhood $\mathcal U$ of $(\bar x,0)$ in $T\mathcal M$ it maps into $\mathcal M$ and is of class $C^{k-1}$, $r(x,0)=x$ and $\mathrm Dr(x,\cdot)(0)=\mathrm{id}_{T_{\mathcal M}(x)}$ for $(x,0)\in\mathcal U$.
--
--   The projective retraction is the reference example of a retraction for Riemannian optimization on submanifolds, and the model the paper's retractor construction (Section 4) generalizes.
--
--   **Formalization Note** The page's $R$ is set-valued by definition of $P_{\mathcal M}$; item 1 states that it is single-valued near $(\bar x,0)$, which the page takes from Lemma 3.1, and item 2 states that this single value is a retraction. "Near $(\bar x,0)$ in $T\mathcal M$" is the filter `𝓝[tangentBundle M] (xbar, 0)`.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 8, Proposition 3.2, display (3.4)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ProjLikeRetr_Projective_IsRetractionAt

open RandomGradFree.Nonsmooth
open scoped Topology

namespace ProjLikeRetr.Projective

/-- Proposition 3.2, p. 8 (Projective retraction): if `M` is a `C^k` submanifold (`k ≥ 2`)
around `x̄ ∈ M`, then near `(x̄, 0)` in the tangent bundle the set `P_M(x + u)` is a single
point `r (x, u)`, and `r`, i.e. `R(x, u) = P_M(x + u)`, is a retraction on `M` around `x̄`. -/
theorem projective_retraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ r : E × E → E,
      (∀ᶠ p in 𝓝[ProjLikeRetr.Retractor.tangentBundle M] (xbar, 0), {z | IsMetricProjection M (p.1 + p.2) z} = {r p}) ∧
      IsRetractionAt k M r xbar := by sorry

end ProjLikeRetr.Projective
