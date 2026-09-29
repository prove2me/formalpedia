-- Prove2me | Theorems.Thm_SPOBounds_StronglyConvex_nu_eq_norm
-- name    : SPOBounds.StronglyConvex.nu_eq_norm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:38:44.501934+00:00
-- url     : https://prove2.me/theorems/8479f500-583e-4e14-91d0-ca057314009d
-- title:
--   Theorem 7, first claim — for strongly convex $S$, $\nu_S(\hat c)=\|\hat c\|_*$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and let $S\subseteq E$ be compact, not a singleton, and $\bar\mu$-strongly convex for some $\bar\mu>0$. Then the distance to degeneracy equals the dual norm:
--   $$\nu_S(\hat c)=\|\hat c\|_*\qquad\text{for every cost vector } \hat c.$$
--
--   Hence for strongly convex feasible regions the margin $\nu_S(\hat c)$ of a prediction, which enters the margin SPO loss, is as easy to compute as the dual norm itself.
--
--   **Formalization Note** $\nu_S$ is the infimum distance, in the operator norm of `StrongDual ℝ E`, to the degenerate set. Compactness is the paper's standing assumption (§2, p. 5); non-emptiness follows from `S.Nontrivial`.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 23, Theorem 7, first claim

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Theorem 7, first claim, p. 23: for a compact, `μ̄`-strongly convex set `S` with `μ̄ > 0`
that is not a singleton, the distance to degeneracy is the dual norm: `ν_S(ĉ) = ‖ĉ‖_*` for
every cost vector `ĉ`. -/
theorem nu_eq_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S) :
    ∀ chat : StrongDual ℝ E, SPOBounds.Shared.nu S chat = ‖chat‖ := by sorry

end SPOBounds.StronglyConvex
