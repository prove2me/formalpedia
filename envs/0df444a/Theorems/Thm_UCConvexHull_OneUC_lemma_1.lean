-- Prove2me | Theorems.Thm_UCConvexHull_OneUC_lemma_1
-- name    : UCConvexHull.OneUC.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:56.607126+00:00
-- url     : https://prove2.me/theorems/2b2a44ec-ae68-44d7-a276-9277a267c465
-- title:
--   Lemma 1, p. 18 — the 1-sum of closed convex hull descriptions is exact: C¹ ⊕ C² = conv‾(S¹ ⊕ S²) (hypothesis (ii) dropped)
-- statement:
--   For $h=1,2$ let $S^h\subseteq\mathbb R^{n_h}\times\mathbb R$, and let $C^h=\overline{\operatorname{conv}}(S^h)$ be the closure of its convex hull. Assume:
--   1. every point $(x^h,y)\in S^h$ has $y\in\{0,1\}$;
--   2. for $h=1,2$ there are points $(\bar x^h,0)\in S^h$ and $(\tilde x^h,1)\in S^h$.
--
--   Then
--
--   $$C^1\oplus C^2=\overline{\operatorname{conv}}(S^1\oplus S^2),$$
--
--   where $\oplus$ is the 1-sum composition (Definition 1). Gluing two exact descriptions of closed convex hulls along a shared binary variable therefore gives an exact description of the closed convex hull of the glued set. This is the composition step from which Theorem 1 is built.
--
--   **Formalization Note.**
--   1. The paper's hypothesis (i), that the closed convex sets $C^h=\{(x^h,y): y\ge 0,\ f^h(x^h,y)\le 0\}$ (25) describe the convex hull of $S^h$, is stated as the set equation $C^h=\overline{\operatorname{conv}}(S^h)$, without the representing functions $f^h$.
--   2. The paper's hypothesis (ii), Assumption 1 (the KKT conditions of the representation $f^h$ are necessary and sufficient for optimality), is dropped. It constrains only how $C^h$ is written, not the set $C^h$, and the set identity holds without it, so dropping it strengthens the lemma. Keeping it would require a subdifferential of vector-valued constraint functions.
--   3. Hypothesis (iv) (points with $y=0$ and with $y=1$ in both sets) is kept: without it the identity can fail. The remark after the lemma on p. 18, which says the result "clearly holds in general", is not formalized.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), p. 18, Lemma 1, (25); proof in Appendix A, pp. 30–34

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_HullTools

namespace UCConvexHull.OneUC

/-- Lemma 1 (p. 18), without hypothesis (ii): if `Cʰ` is the closure of the convex hull of `Sʰ`
(i), every point of `Sʰ` has `y ∈ {0, 1}` (iii), and `Sʰ` has points with `y = 0` and with `y = 1`
(iv), for `h = 1, 2`, then `C¹ ⊕ C²` is the closure of the convex hull of `S¹ ⊕ S²`. -/
theorem lemma_1 {n₁ n₂ : ℕ} (S₁ : Set ((Fin n₁ → ℝ) × ℝ)) (S₂ : Set ((Fin n₂ → ℝ) × ℝ))
    (C₁ : Set ((Fin n₁ → ℝ) × ℝ)) (C₂ : Set ((Fin n₂ → ℝ) × ℝ))
    (hC₁ : C₁ = closure (convexHull ℝ S₁)) (hC₂ : C₂ = closure (convexHull ℝ S₂))
    (hy₁ : ∀ q ∈ S₁, q.2 = 0 ∨ q.2 = 1) (hy₂ : ∀ q ∈ S₂, q.2 = 0 ∨ q.2 = 1)
    (h0₁ : ∃ x, (x, (0 : ℝ)) ∈ S₁) (h1₁ : ∃ x, (x, (1 : ℝ)) ∈ S₁)
    (h0₂ : ∃ x, (x, (0 : ℝ)) ∈ S₂) (h1₂ : ∃ x, (x, (1 : ℝ)) ∈ S₂) :
    oneSum C₁ C₂ = closure (convexHull ℝ (oneSum S₁ S₂)) := by sorry

end UCConvexHull.OneUC
