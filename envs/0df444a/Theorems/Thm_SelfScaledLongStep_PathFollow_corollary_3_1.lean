-- Prove2me | Theorems.Thm_SelfScaledLongStep_PathFollow_corollary_3_1
-- name    : SelfScaledLongStep.PathFollow.corollary_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:47.071977+00:00
-- url     : https://prove2.me/theorems/fbca0076-5ca9-4ce3-a95b-0eab1febe741
-- title:
--   Corollary 3.1, p. 11 — for v, z ∈ int K some w ∈ int K has F′(v) = −F″(w)z, F′(z) = −F″(w)v, F′(v) − F′(z) = F″(w)(v − z)
-- statement:
--   Throughout, $K\subset E=\mathbb R^n$ is a closed convex pointed cone with nonempty interior and $F$ is a $\nu$-self-scaled barrier for $K$ (Definition 2.1). Let $v,z\in\operatorname{int}K$. Then there is a point $w\in\operatorname{int}K$ such that
--   $$F'(v)=-F''(w)z,\qquad F'(z)=-F''(w)v,$$
--   and therefore
--   $$F'(v)-F'(z)=F''(w)(v-z).$$
--
--   The corollary is a mean-value identity for the gradient of a self-scaled barrier, with an exact intermediate Hessian at a single interior point; it is the starting point of the second-order estimate of Theorem 4.3.
--
--   **Formalization Note** The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 11, Corollary 3.1

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Corollary 3.1** (p. 11). For any `v, z ∈ int K` there is `w ∈ int K` with
`F'(v) = −F''(w)z`; moreover `F'(z) = −F''(w)v`, and therefore `F'(v) − F'(z) = F''(w)(v − z)`. -/
theorem corollary_3_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (v z : EuclideanSpace ℝ (Fin n)) (hv : v ∈ interior K) (hz : z ∈ interior K) :
    ∃ w ∈ interior K, gradient F v = -(hess F w z) ∧ gradient F z = -(hess F w v) ∧
      gradient F v - gradient F z = hess F w (v - z) := by sorry

end SelfScaledLongStep.PathFollow
