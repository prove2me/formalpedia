-- Prove2me | Theorems.Thm_ProjLikeRetr_Retractor_lemma_4_8
-- name    : ProjLikeRetr.Retractor.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:28:59.977809+00:00
-- url     : https://prove2.me/theorems/c1956997-cc6f-4dad-97de-3b407349ced5
-- title:
--   Lemma 4.8, p. 18 — straightening up: D(x,u) = {v + A(x,u)v : v ∈ N_M(x)} with A of class C^{k−1}
-- statement:
--   Let $\mathcal M$ be a $d$-dimensional submanifold of class $C^k$ ($k\ge2$) of an $n$-dimensional Euclidean space $\mathcal E$, and let $D$ be a retractor on $\mathcal M$ (Definition 4.1). Then there are a neighbourhood $\mathcal U_{\mathrm T\mathcal M}$ of the zero section in $\mathrm T\mathcal M$ and, for each $(x,u)\in\mathcal U_{\mathrm T\mathcal M}$, a linear map $A(x,u):\mathrm N_{\mathcal M}(x)\to\mathrm T_{\mathcal M}(x)$, depending on $(x,u)$ in a $C^{k-1}$ way, such that for all $(x,u)\in\mathcal U_{\mathrm T\mathcal M}$
--
--   $$D(x,u)=\{v+A(x,u)v:\ v\in\mathrm N_{\mathcal M}(x)\}.$$
--
--   Moreover $A(x,u)$ is unique: any linear map $A'$ from $\mathrm N_{\mathcal M}(x)$ into $\mathrm T_{\mathcal M}(x)$ with $D(x,u)=\{v+A'v:v\in\mathrm N_{\mathcal M}(x)\}$ coincides with $A(x,u)$ on $\mathrm N_{\mathcal M}(x)$.
--
--   The lemma writes the field of subspaces $D(x,u)$ as a graph over the normal space; this is what lets the general case of Theorem 4.2 be reduced to the normal case of Lemma 4.7.
--
--   **Formalization Note** The page's map $\mathcal A:(x,u,v)\mapsto(x,A(x,u)v)$ on $\mathcal U_{\mathrm T\mathcal M}\oplus\mathrm N\mathcal M$ is encoded by extending $A(x,u)$ by $0$ on $\mathrm T_{\mathcal M}(x)$ (i.e. using $A(x,u)\circ P_{\mathrm N_{\mathcal M}(x)}$), which gives an operator $A(x,u)\in L(\mathcal E)$; $C^{k-1}$ dependence of this operator on $(x,u)\in O\cap\mathrm T\mathcal M$ is equivalent to $\mathcal A$ being $C^{k-1}$, because $x\mapsto P_{\mathrm N_{\mathcal M}(x)}$ is $C^{k-1}$. Uniqueness is stated pointwise on $\mathrm N_{\mathcal M}(x)$, for competitors given as operators on $\mathcal E$ mapping $\mathrm N_{\mathcal M}(x)$ into $\mathrm T_{\mathcal M}(x)$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 18, Lemma 4.8

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ProjLikeRetr_Retractor_IsRetractor

namespace ProjLikeRetr.Retractor

/-- Lemma 4.8, p. 18 (straightening up). Let `D` be a retractor on the `d`-dimensional `C^k`
submanifold `M` (`k ≥ 2`). There are a neighbourhood `O ∩ TM` of the zero section of `TM` and a
`C^{k-1}` family of linear maps `A(x, u)`, sending `N_M(x)` into `T_M(x)` (and extended by `0` on
`T_M(x)`), such that `D(x, u) = {v + A(x, u) v : v ∈ N_M(x)}` for all `(x, u) ∈ O ∩ TM`; and
`A(x, u)` is unique on `N_M(x)` with these properties. -/
theorem lemma_4_8 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (D : E × E → Submodule ℝ E)
    (hk : 2 ≤ k) (hM : IsSubmanifold k d M) (hD : IsRetractor k d M D) :
    ∃ O : Set (E × E), IsOpen O ∧ (∀ x ∈ M, (x, (0 : E)) ∈ O) ∧
      ∃ A : E × E → (E →L[ℝ] E),
        ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) A (O ∩ tangentBundle M) ∧
        ∀ p ∈ O ∩ tangentBundle M,
          (∀ v ∈ normalSpace M p.1, A p v ∈ tangentSpace M p.1) ∧
          (∀ u ∈ tangentSpace M p.1, A p u = 0) ∧
          (D p : Set E) = {y | ∃ v ∈ normalSpace M p.1, y = v + A p v} ∧
          ∀ A' : E →L[ℝ] E, (∀ v ∈ normalSpace M p.1, A' v ∈ tangentSpace M p.1) →
            (D p : Set E) = {y | ∃ v ∈ normalSpace M p.1, y = v + A' v} →
            ∀ v ∈ normalSpace M p.1, A' v = A p v := by sorry

end ProjLikeRetr.Retractor
