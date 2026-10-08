-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_lemma_3_1
-- name    : SelfScaledLongStep.PrimalDual.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:24.191756+00:00
-- url     : https://prove2.me/theorems/b922514e-7754-4754-98b5-6c079ddd34b0
-- title:
--   Lemma 3.1, p. 11 — for fixed v ∈ K, g(x) = −⟨F′(x), v⟩ is convex on int K
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$, and fix $v\in K$ (a boundary point is allowed). Then the function
--   $$g(x)=-\langle F'(x),v\rangle$$
--   is convex on $\operatorname{int}K$.
--
--   The lemma is the source of the sign information on third derivatives of a self-scaled barrier (Corollary 3.2) and of the separability results of §5.
--
--   **Formalization Note** $E^*\cong E=\mathbb R^n$, $F'(x)$ is `gradient F x`. Convexity is Mathlib's `ConvexOn` on the convex set $\operatorname{int}K$. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 11, Lemma 3.1

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Lemma 3.1** (p. 11). For fixed `v ∈ K` (boundary included) the function
`g(x) = −⟨F'(x), v⟩` is convex on `int K`. -/
theorem lemma_3_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ K) :
    ConvexOn ℝ (interior K) (fun x => -⟪gradient F x, v⟫_ℝ) := by sorry

end SelfScaledLongStep.PrimalDual
