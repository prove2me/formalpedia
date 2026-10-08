-- Prove2me | Theorems.Thm_ProjLikeRetr_Retractor_lemma_4_7
-- name    : ProjLikeRetr.Retractor.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:29:33.684187+00:00
-- url     : https://prove2.me/theorems/920ee650-d19a-4c2e-8088-82bce05ba18a
-- title:
--   Lemma 4.7, p. 17 — the special case D(x,u) = N_M(x): the smallest normal correction defines a retraction
-- statement:
--   Let $\mathcal M$ be a $d$-dimensional submanifold of class $C^k$ ($k\ge2$) of an $n$-dimensional Euclidean space $\mathcal E$, with tangent spaces $\mathrm T_{\mathcal M}(x)$, normal spaces $\mathrm N_{\mathcal M}(x)$ and tangent bundle $\mathrm T\mathcal M$.
--
--   1. For every $\bar x\in\mathcal M$ there are a neighbourhood $\mathcal U_{\mathrm T\mathcal M}$ of $(\bar x,0)$ in $\mathrm T\mathcal M$ and a map $v$ such that, for every $(x,u)\in\mathcal U_{\mathrm T\mathcal M}$, $v(x,u)$ is the one and only smallest $v\in\mathrm N_{\mathcal M}(x)$ with $x+u+v\in\mathcal M$; moreover $\mathrm D_u v(x,0)=0$ whenever $(x,0)\in\mathcal U_{\mathrm T\mathcal M}$, and
--
--   $$R(x,u)=x+u+v(x,u)$$
--
--   is a retraction on $\mathcal M$ around $\bar x$ (Definition 2.1).
--   2. Consequently, any map $R$ with $R(x,u)=x+u+v$ whenever $(x,u)\in\mathrm T\mathcal M$ and $v$ is the unique smallest normal correction at $(x,u)$ is a retraction on $\mathcal M$: the expression of $R$ depends neither on $\bar x$ nor on the neighbourhood.
--
--   This is Theorem 4.2 for the orthographic retractor $D(x,u)=\mathrm N_{\mathcal M}(x)$, and the first step of its proof.
--
--   **Formalization Note** The neighbourhood is $O\cap\mathrm T\mathcal M$ with $O$ open in $\mathcal E\times\mathcal E$. "$\mathrm D_u v(x,0)=0$" is the derivative at $0$ of $u\mapsto v(x,u)$ on the vector space $\mathrm T_{\mathcal M}(x)$. Part 2 is the lemma's last sentence, stated for every map that selects the unique smallest correction wherever it exists.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 17, Lemma 4.7

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ProjLikeRetr_Retractor_IsRetraction
import Definitions.Def_ProjLikeRetr_Retractor_IsSmallestNormalCorrection

namespace ProjLikeRetr.Retractor

/-- Lemma 4.7, p. 17 (special case `D(x, u) = N_M(x)`). Let `M` be a `d`-dimensional `C^k`
submanifold (`k ≥ 2`) of the Euclidean space `E`.
* For every `x̄ ∈ M` there is a neighbourhood `O ∩ TM` of `(x̄, 0)` in `TM` such that, for every
  `(x, u)` in it, there is one and only one smallest `v(x, u) ∈ N_M(x)` with
  `x + u + v(x, u) ∈ M`; moreover `D_u v(x, 0) = 0` and `R(x, u) = x + u + v(x, u)` is a
  retraction around `x̄`.
* Consequently every `R` with `R(x, u) = x + u + v` whenever `v` is the unique smallest normal
  correction at `(x, u) ∈ TM` is a retraction on `M`. -/
theorem lemma_4_7 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E)
    (hk : 2 ≤ k) (hM : IsSubmanifold k d M) :
    (∀ xbar ∈ M, ∃ O : Set (E × E), IsOpen O ∧ (xbar, 0) ∈ O ∧
      ∃ v : E × E → E,
        (∀ p ∈ O ∩ tangentBundle M, IsSmallestNormalCorrection M p (v p) ∧
          ∀ w : E, IsSmallestNormalCorrection M p w → w = v p) ∧
        (∀ x : E, (x, 0) ∈ O ∩ tangentBundle M →
          HasFDerivAt (fun u : tangentSpace M x => v (x, (u : E)))
            (0 : tangentSpace M x →L[ℝ] E) 0) ∧
        IsRetractionAt k M (fun p => p.1 + p.2 + v p) xbar) ∧
    (∀ R : E × E → E,
      (∀ p ∈ tangentBundle M, ∀ v : E, IsSmallestNormalCorrection M p v →
        (∀ w : E, IsSmallestNormalCorrection M p w → w = v) → R p = p.1 + p.2 + v) →
      IsRetraction k M R) := by sorry

end ProjLikeRetr.Retractor
