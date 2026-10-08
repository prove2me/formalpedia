-- Prove2me | Theorems.Thm_ProjLikeRetr_Retractor_retractor_gives_retraction
-- name    : ProjLikeRetr.Retractor.retractor_gives_retraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:29:16.627475+00:00
-- url     : https://prove2.me/theorems/d94c21cd-b052-4ad2-88c5-06d8350f0e9d
-- title:
--   Theorem 4.2, pp. 15–16 — retractors give retractions
-- statement:
--   Let $\mathcal M$ be a $d$-dimensional submanifold of class $C^k$ ($k\ge2$) of an $n$-dimensional Euclidean space $\mathcal E$, and let $D$ be a retractor on $\mathcal M$ (Definition 4.1). For $(x,u)$ in the tangent bundle $\mathrm T\mathcal M$, let $\mathcal D(x,u)=x+u+D(x,u)$ and let $R(x,u)$ be the set of points of $\mathcal M\cap\mathcal D(x,u)$ nearest to $x+u$. Then $R$ is a retraction on $\mathcal M$. Precisely: for every $\bar x\in\mathcal M$ there is a map $r$ such that
--
--   $$R(x,u)=\{r(x,u)\}\quad\text{for all }(x,u)\in\mathrm T\mathcal M\text{ near }(\bar x,0),$$
--
--   and $r$ is a retraction on $\mathcal M$ around $\bar x$ (Definition 2.1). In particular $R$ maps a neighbourhood of $(\bar x,0)$ in $\mathrm T\mathcal M$ to singletons.
--
--   The retraction $R$ is called the retraction induced by $D$. The theorem turns the construction of retractions — the basic tool of Newton and gradient methods on matrix manifolds — into the choice of a smooth field of admissible directions transverse to the tangent space; the orthographic retraction ($D=\mathrm N_{\mathcal M}(x)$) and the projective retraction ($D=\mathrm N_{\mathcal M}(P_{\mathcal M}(x+u))$) are special cases.
--
--   **Formalization Note** "Near $(\bar x,0)$ in $\mathrm T\mathcal M$" is the filter $\mathcal N_{\mathrm T\mathcal M}(\bar x,0)$ (neighbourhoods within $\mathrm T\mathcal M$). The singleton claim is an equality of sets, so it also asserts that $R(x,u)$ is nonempty. $D$ is a total map into subspaces of $\mathcal E$; the retractor hypothesis only constrains it near the zero section.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, pp. 15–16, Theorem 4.2

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ProjLikeRetr_Retractor_IsRetraction
import Definitions.Def_ProjLikeRetr_Retractor_IsRetractor
import Definitions.Def_ProjLikeRetr_Retractor_retractorR

open Filter Topology

namespace ProjLikeRetr.Retractor

/-- Theorem 4.2, pp. 15–16 (retractors give retractions). Let `M` be a `d`-dimensional `C^k`
submanifold (`k ≥ 2`) of the Euclidean space `E` and `D` a retractor on `M`. For every
`x̄ ∈ M`, the set `R(x, u)` of points of `M ∩ (x + u + D(x, u))` nearest to `x + u` is a
singleton `{r(x, u)}` for all `(x, u)` of `TM` near `(x̄, 0)`, and `r` is a retraction on `M`
around `x̄`. Hence `R` is a retraction on `M`. -/
theorem retractor_gives_retraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (D : E × E → Submodule ℝ E)
    (hk : 2 ≤ k) (hM : IsSubmanifold k d M) (hD : IsRetractor k d M D) :
    ∀ xbar ∈ M, ∃ r : E × E → E,
      (∀ᶠ p in 𝓝[tangentBundle M] (xbar, 0), retractorR M D p = {r p}) ∧
      IsRetractionAt k M r xbar := by sorry

end ProjLikeRetr.Retractor
