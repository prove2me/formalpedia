-- Prove2me | Theorems.Thm_ProximalBanach_Hybrid_thm6_rockafellar_maximal_iff
-- name    : ProximalBanach.Hybrid.thm6_rockafellar_maximal_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:08:12.817634+00:00
-- url     : https://prove2.me/theorems/8e126235-2403-4c8c-9a8a-03923963c79d
-- title:
--   Theorem 6 (Rockafellar) — T is maximal monotone iff R(J + rT) = E* for all r > 0
-- statement:
--   Let $E$ be a reflexive, strictly convex and smooth real Banach space with duality mapping $J$, and let $T:E\to2^{E^*}$ be a monotone operator. Then $T$ is maximal if and only if
--   $$R(J+rT)=E^*\qquad\text{for all } r>0,$$
--   that is, for every $r>0$ and every $f\in E^*$ there exist $x\in E$ and $w\in Tx$ with $Jx+rw=f$.
--
--   This surjectivity is what makes the implicit proximal step $0=v_n+\frac1{r_n}(Jy_n-Jx_n)$, $v_n\in Ty_n$, of the algorithm (3.1) solvable.
--
--   **Formalization Note** $T$ is only assumed monotone here: the section's standing assumption that $T$ is maximal is lifted, as the theorem characterizes maximality.
-- source:
--   Kamimura and Takahashi, Strong convergence of a proximal-type algorithm in a Banach space, SIAM J. Optim. 13(3), 2003, p. 942, Theorem 6 (quoted from Rockafellar [9])

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Theorem 6 (p. 942, Rockafellar): in a reflexive, strictly convex, smooth Banach space,
a monotone operator `T` is maximal iff `R(J + rT) = E*` for all `r > 0`. -/
theorem thm6_rockafellar_maximal_iff [StrictConvexSpace ℝ E] (hR : IsReflexive E)
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) :
    IsMaximalMonotone T ↔
      ∀ r : ℝ, 0 < r → ∀ f : StrongDual ℝ E, ∃ x : E, ∃ w ∈ T x, J x + r • w = f := by sorry

end ProximalBanach.Hybrid
