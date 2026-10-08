-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_lemma_2_4
-- name    : SkutellaCQP.NoRel.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:59.458997+00:00
-- url     : https://prove2.me/theorems/7bc9ba33-c2b6-458e-8e3c-fb71066c1c3a
-- title:
--   Lemma 2.4, p. 11 — a ↦ (1−γ)cᵀa + ½aᵀ(D + 2γ·diag(c))a is convex for all instances iff γ ≥ ½
-- statement:
--   For a real parameter $\gamma$, consider the function on $\mathbb R^{mn}$
--
--   $$
--   a\;\longmapsto\;(1-\gamma)\cdot c^Ta+\tfrac12a^T\bigl(D+2\gamma\cdot\operatorname{diag}(c)\bigr)a ,
--   $$
--
--   built from an instance of $R\,|\,|\sum w_jC_j$ with $c_{ij}=w_jp_{ij}$ and $D$ as in (4). This function is convex for arbitrary instances (all $m$, $n$, all $p_{ij}>0$, $w_j\ge 0$) if and only if $\gamma\ge\tfrac12$.
--
--   The lemma identifies $\gamma=\tfrac12$ as the smallest amount by which the diagonal of $D$ must be raised to make the (QP) objective convex for every instance; it motivates the relaxation (CQP).
--
--   **Formalization Note** The quantifier over instances sits inside the equivalence: for a single fixed instance the "only if" direction is false. The page's surrounding text restricts to $0<\gamma\le 1$, but the lemma itself has no range and the equivalence holds for every real $\gamma$, so $\gamma$ is unrestricted. Convexity is `ConvexOn ℝ Set.univ` on functions `Fin m × Fin n → ℝ`.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 11, Lemma 2.4

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

open Matrix

/-- Lemma 2.4 (p. 11). The function `a ↦ (1 - γ) c^T a + ½ a^T (D + 2γ diag(c)) a` on `ℝ^{mn}` is
convex for every instance of `R | | ∑ w_j C_j` if and only if `γ ≥ ½`. -/
theorem lemma_2_4 (γ : ℝ) :
    (∀ (m n : ℕ) (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ), (∀ i j, 0 < p i j) → (∀ j, 0 ≤ w j) →
      ConvexOn ℝ Set.univ (fun x : Fin m × Fin n → ℝ =>
        (1 - γ) * (cvec p w ⬝ᵥ x) +
          (1 / 2) * (x ⬝ᵥ ((Dmat p w + (2 * γ) • Matrix.diagonal (cvec p w)) *ᵥ x)))) ↔
    1 / 2 ≤ γ := by sorry

end SkutellaCQP.NoRel
