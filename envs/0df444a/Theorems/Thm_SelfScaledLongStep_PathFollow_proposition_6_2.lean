-- Prove2me | Theorems.Thm_SelfScaledLongStep_PathFollow_proposition_6_2
-- name    : SelfScaledLongStep.PathFollow.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:45.946494+00:00
-- url     : https://prove2.me/theorems/aa175b43-8215-4ea9-84a7-6dffb7e03172
-- title:
--   Proposition 6.2, p. 23 — the projection p(u) of u into ker A w.r.t. F″(w) satisfies ‖p(u)‖²_w = ⟨u, p(u)⟩
-- statement:
--   Throughout, $K\subset E=\mathbb R^n$ is a closed convex pointed cone with nonempty interior and $F$ is a $\nu$-self-scaled barrier for $K$ (Definition 2.1). Let $A:E\to Y$ be a surjective linear map, $w\in\operatorname{int}K$ and $u\in E^*$. If $(y(u),p(u))$ solves
--   $$Ap(u)=0,\qquad A^*y(u)+F''(w)p(u)=u, \tag{6.4}$$
--   so that $p(u)$ is the projection of $u$ into the kernel of $A$ with respect to the positive definite operator $F''(w)$, then
--   $$\|p(u)\|_w^2=\langle u,p(u)\rangle . \tag{6.5}$$
--
--   With $u=\tau c+F'(x)$ this identity is what turns the decrease of the penalty function in Theorem 9.1 into a statement about the proximity measure.
--
--   **Formalization Note** Surjectivity of $A$ is the standing assumption (6.1) of §6. The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 23, Proposition 6.2, (6.4)–(6.5)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Proposition 6.2** (p. 23), (6.5). If `p = p(u)` is the projection of `u` into `ker A`
with respect to `F''(w)` (system (6.4), `w ∈ int K`), then `‖p(u)‖²_w = ⟨u, p(u)⟩`. -/
theorem proposition_6_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : SelfScaledLongStep.PrimalDual.IsProjection F A w u y p) :
    (lnorm F w p) ^ 2 = ⟪u, p⟫_ℝ := by sorry

end SelfScaledLongStep.PathFollow
