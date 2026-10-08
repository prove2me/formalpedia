-- Prove2me | Theorems.Thm_ProjLikeRetr_Projective_tangent_normalBundle
-- name    : ProjLikeRetr.Projective.tangent_normalBundle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:38:18.694418+00:00
-- url     : https://prove2.me/theorems/1c83a248-3e56-4ea7-8477-f7d7562dfc5a
-- title:
--   (3.3), proof of Lemma 3.1, p. 7 — the tangent space of NM at (x̄, 0) is T_M(x̄) × N_M(x̄)
-- statement:
--   Let $\mathcal M$ be a submanifold of the Euclidean space $\mathcal E$ of class $C^k$ ($k\ge2$) and dimension $d$ around $\bar x\in\mathcal M$, and let $N\mathcal M\subseteq\mathcal E\times\mathcal E$ be its normal bundle. Then the tangent space of $N\mathcal M$ at $(\bar x,0)$ is
--
--   $$T_{N\mathcal M}(\bar x,0)=T_{\mathcal M}(\bar x)\times N_{\mathcal M}(\bar x).$$
--
--   In the proof of Lemma 3.1 this identifies the derivative at $(\bar x,0)$ of $F:N\mathcal M\to\mathcal E$, $(x,v)\mapsto x+v$, as the invertible map $(u,v)\mapsto u+v$.
--
--   **Formalization Note** The tangent space of $N\mathcal M$ uses the same convention as for $\mathcal M$: the linear span of the tangent cone of $N\mathcal M$ at $(\bar x,0)$ in $\mathcal E\times\mathcal E$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 7, proof of Lemma 3.1, display (3.3)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ProjLikeRetr.Projective

/-- (3.3), proof of Lemma 3.1, p. 7: the tangent space at `(x̄, 0)` of the normal bundle `NM`
(a `C^{k-1}` submanifold of `E × E`) is `T_M(x̄) × N_M(x̄)`. -/
theorem tangent_normalBundle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    Submodule.span ℝ (tangentConeAt ℝ (ProjLikeRetr.Retractor.normalBundle M) (xbar, 0)) =
      (ProjLikeRetr.Retractor.tangentSpace M xbar).prod (ProjLikeRetr.Retractor.normalSpace M xbar) := by sorry

end ProjLikeRetr.Projective
