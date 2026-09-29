-- Prove2me | Theorems.Thm_SPOBounds_StronglyConvex_strength_property
-- name    : SPOBounds.StronglyConvex.strength_property
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:39:14.856988+00:00
-- url     : https://prove2.me/theorems/236c0b1f-c5ba-4118-9387-075b46a38413
-- title:
--   Theorem 7 — strongly convex sets satisfy the strength property with $\mu=\bar\mu$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and let the feasible region $S\subseteq E$ be compact, not a singleton, and $\bar\mu$-strongly convex for some $\bar\mu>0$. Let $w^*$ be any optimization oracle for $S$: for every cost vector $\hat c$, $w^*(\hat c)\in S$ and $\hat c^\top w^*(\hat c)\le\hat c^\top w$ for all $w\in S$. Then $S$ satisfies the strength property with parameter $\mu=\bar\mu$:
--   $$\hat c^\top\big(w-w^*(\hat c)\big)\ \ge\ \Big(\frac{\bar\mu\,\nu_S(\hat c)}{2}\Big)\|w-w^*(\hat c)\|^2\qquad\text{for all } w\in S \text{ and all } \hat c.$$
--
--   Combined with the paper's margin-based generalization bounds (Theorems 4 and 5), this makes those bounds applicable to every strongly convex feasible region, with strength parameter equal to the strong convexity constant.
--
--   **Formalization Note** The oracle is arbitrary (no tie-breaking rule is fixed), so the statement holds for every oracle; one exists because $S$ is nonempty and compact. Compactness is the paper's standing assumption (§2, p. 5); convexity is part of the strongly convex set predicate; non-emptiness follows from `S.Nontrivial`.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 23, Theorem 7 (strength claim; proof p. 24)

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Theorem 7, strength claim, p. 23: if the compact set `S` is not a singleton and is
`μ̄`-strongly convex for some `μ̄ > 0`, then for every optimization oracle `w`
(`w ĉ ∈ S` minimizes `v ↦ ĉ v` over `S`) the strength property (5) holds with `μ = μ̄`. -/
theorem strength_property {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ v ∈ S, c (w c) ≤ c v) :
    SPOBounds.Shared.StrengthProperty S μbar w := by sorry

end SPOBounds.StronglyConvex
