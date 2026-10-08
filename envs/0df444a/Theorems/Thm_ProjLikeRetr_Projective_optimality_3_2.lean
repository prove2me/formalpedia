-- Prove2me | Theorems.Thm_ProjLikeRetr_Projective_optimality_3_2
-- name    : ProjLikeRetr.Projective.optimality_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:38:21.76989+00:00
-- url     : https://prove2.me/theorems/0c1c1cfb-31f5-49f3-9ddc-7d5f8f0b2507
-- title:
--   (3.2), §3.1, p. 6 — a projection p of x onto M satisfies p ∈ M and x − p ∈ N_M(p)
-- statement:
--   Let $\mathcal E$ be a Euclidean space, $\mathcal M\subseteq\mathcal E$ and $x\in\mathcal E$. Let $p$ be a point of the projection $P_{\mathcal M}(x)=\operatorname{argmin}\{\|x-y\|:y\in\mathcal M\}$, and suppose that $\mathcal M$ is a submanifold of $\mathcal E$ of class $C^k$ ($k\ge2$) and dimension $d$ around $p$. Then $p$ satisfies the first-order optimality conditions of the minimization problem defining $P_{\mathcal M}(x)$:
--
--   $$p\in\mathcal M,\qquad x-p\in N_{\mathcal M}(p).$$
--
--   This is the characterization used in the proof of Lemma 3.1: a nearest point $p$ is recovered from $x$ as the first component of the inverse of $(p,v)\mapsto p+v$ on the normal bundle.
--
--   **Formalization Note** The submanifold hypothesis is taken around $p$: for an arbitrary set only $\langle x-p,u\rangle\le0$ on the tangent cone holds, and orthogonality to the whole tangent space needs a submanifold.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 6, §3.1, display (3.2)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Projective

/-- (3.2), §3.1, p. 6: if `p ∈ P_M(x)` and `M` is a `C^k` submanifold (`k ≥ 2`) around `p`,
then `p ∈ M` and `x - p ∈ N_M(p)`. -/
theorem optimality_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (x p : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M p) (hp : IsMetricProjection M x p) :
    p ∈ M ∧ x - p ∈ ProjLikeRetr.Retractor.normalSpace M p := by sorry

end ProjLikeRetr.Projective
