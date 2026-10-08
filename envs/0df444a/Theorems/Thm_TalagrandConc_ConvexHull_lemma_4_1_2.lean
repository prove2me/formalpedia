-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_lemma_4_1_2
-- name    : TalagrandConc.ConvexHull.lemma_4_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:11.46443+00:00
-- url     : https://prove2.me/theorems/a0fcaec7-def1-4af4-99be-9b0f5bb06415
-- title:
--   Lemma 4.1.2 — $x\in A_t^c$ iff every weighted Hamming distance to $A$ is at most $t\|\alpha\|_2$
-- statement:
--   Let $A\subseteq\Omega^N$, $x\in\Omega^N$ and $t\ge0$, and let $A_t^c=\{x;\ f_c(A,x)\le t\}$ be the convex-hull enlargement of $A$. Then the following are equivalent:
--
--   1. $x\in A_t^c$;
--   2. for every family of real numbers $(\alpha_i)_{i\le N}$ there exists $y\in A$ with
--   $$\sum_{i\le N}\{\alpha_i;\ x_i\ne y_i\}\le t\sqrt{\sum_{i\le N}\alpha_i^2},$$
--   where the left side is the sum of the $\alpha_i$ over the coordinates in which $x$ and $y$ differ.
--
--   The lemma explains the enlargement $A_t^c$: a point is close to $A$ in the convex hull distance exactly when it is close to $A$ for every weighted Hamming distance simultaneously, with the weight vector normalised in $\ell^2$. This is what makes Theorem 4.1.1 applicable with weights chosen after seeing $x$.
--
--   **Formalization Note** $t\ge0$ is assumed (the paper uses $A_t^c$ only for $t\ge0$; for $N=0$ and $t<0$ the two conditions differ). The weights are arbitrary reals, as printed. $\Omega$ carries decidable equality so the sum over $\{i;\ x_i\ne y_i\}$ is a `Finset` sum.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 124, Lemma 4.1.2, Eqs. (4.1.4)–(4.1.5)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

/-- Talagrand (1995), p. 124, Lemma 4.1.2: for `t ≥ 0`, `x ∈ A_t^c` (Eq. (4.1.4)) iff for every
real family `(α_i)_{i ≤ N}` there is `y ∈ A` with
`Σ { α_i ; x_i ≠ y_i } ≤ t (Σ_i α_i²)^{1/2}` (Eq. (4.1.5)). -/
theorem lemma_4_1_2 {Ω : Type*} [DecidableEq Ω] {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) (t : ℝ) (ht : 0 ≤ t) :
    x ∈ enlarge A t ↔
      ∀ a : Fin N → ℝ, ∃ y ∈ A,
        (∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), a i) ≤ t * Real.sqrt (∑ i, a i ^ 2) := by sorry

end TalagrandConc.ConvexHull
