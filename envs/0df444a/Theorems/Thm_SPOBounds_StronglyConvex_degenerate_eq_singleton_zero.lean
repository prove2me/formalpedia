-- Prove2me | Theorems.Thm_SPOBounds_StronglyConvex_degenerate_eq_singleton_zero
-- name    : SPOBounds.StronglyConvex.degenerate_eq_singleton_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:38:10.305983+00:00
-- url     : https://prove2.me/theorems/cd6ed8d6-bd44-4d43-b7c8-9ea27bb03dc2
-- title:
--   For a strongly convex set that is not a singleton, the degenerate set is $\mathcal C^\circ=\{0\}$
-- statement:
--   Let $E$ be a finite-dimensional real normed space and let $S\subseteq E$ be compact, not a singleton (it contains two distinct points), and $\bar\mu$-strongly convex for some $\bar\mu>0$. Then the set of degenerate cost vectors — those $\hat c$ for which $\min_{w\in S}\hat c^\top w$ has more than one optimal solution — is exactly
--   $$\mathcal C^\circ=\{0\}.$$
--
--   The zero functional is degenerate because every point of $S$ minimizes it; every nonzero cost vector has a unique minimizer over a strongly convex set. This is the step to which the proof of Theorem 7 reduces the identity $\nu_S(\hat c)=\|\hat c\|_*$.
--
--   **Formalization Note** Compactness is the paper's standing assumption on the feasible region (§2, p. 5); non-emptiness follows from the non-singleton hypothesis, which is stated as `S.Nontrivial`. Convexity is part of the strongly convex set predicate.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 24, proof of Theorem 7 (first sentence, "it suffices to show that $\mathcal C^\circ=\{0\}$")

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Proof of Theorem 7, p. 24: for a compact, `μ̄`-strongly convex set `S` with `μ̄ > 0` that is
not a singleton, the only degenerate cost vector is `0`, i.e. `𝒞° = {0}`. -/
theorem degenerate_eq_singleton_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S) :
    SPOBounds.Shared.degenerate S = {0} := by sorry

end SPOBounds.StronglyConvex
