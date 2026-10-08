-- Prove2me | Theorems.Thm_SelfScaledLongStep_PathFollow_theorem_4_3
-- name    : SelfScaledLongStep.PathFollow.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:22.161917+00:00
-- url     : https://prove2.me/theorems/9806349b-821d-4a10-9fb9-98e35960b3f3
-- title:
--   Theorem 4.3, p. 18 — ‖F′(v) − F′(x) − F″(x)(v − x)‖∗_v ≤ |v − x|_x · ‖v − x‖_x
-- statement:
--   Throughout, $K\subset E=\mathbb R^n$ is a closed convex pointed cone with nonempty interior and $F$ is a $\nu$-self-scaled barrier for $K$ (Definition 2.1). For any $x,v\in\operatorname{int}K$,
--   $$\bigl\|F'(v)-F'(x)-F''(x)(v-x)\bigr\|^*_v\;\le\;|v-x|_x\cdot\|v-x\|_x .$$
--   Here $\|q\|^*_v=\langle q,[F''(v)]^{-1}q\rangle^{1/2}$ is the dual local norm at $v$, $\|p\|_x=\langle F''(x)p,p\rangle^{1/2}$, and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$.
--
--   The theorem bounds the second-order Taylor remainder of the gradient without any restriction on the distance between $x$ and $v$; it is the key estimate in the analysis of Newton's method (Theorem 9.2) and of the path-following scheme (Theorem 9.3).
--
--   **Formalization Note** The dual norm on the left-hand side is taken at $v$, as printed; the norms on the right at $x$. The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 18, Theorem 4.3

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Theorem 4.3** (p. 18). For `x, v ∈ int K`:
`‖F'(v) − F'(x) − F''(x)(v − x)‖*_v ≤ |v − x|_x · ‖v − x‖_x`.
The dual norm on the left is taken at `v` (`dnorm F v`), the norms on the right at `x`. -/
theorem theorem_4_3 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x v : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hv : v ∈ interior K) :
    dnorm F v (gradient F v - gradient F x - hess F x (v - x)) ≤
      absn K x (v - x) * lnorm F x (v - x) := by sorry

end SelfScaledLongStep.PathFollow
