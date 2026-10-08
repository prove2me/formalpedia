-- Prove2me | Theorems.Thm_SelfScaledLongStep_PathFollow_proposition_6_3
-- name    : SelfScaledLongStep.PathFollow.proposition_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:22.689418+00:00
-- url     : https://prove2.me/theorems/ca31ff14-f2e6-48d2-b7bf-20d056edad0a
-- title:
--   Proposition 6.3, pp. 23–24 — ‖p(u)‖_w ≤ ‖u − A∗y‖∗_w for every y, with equality only at a minimizer
-- statement:
--   Throughout, $K\subset E=\mathbb R^n$ is a closed convex pointed cone with nonempty interior and $F$ is a $\nu$-self-scaled barrier for $K$ (Definition 2.1). Let $A:E\to Y$ be a surjective linear map, $w\in\operatorname{int}K$, $u\in E^*$, and let $p(u)$ be the projection of $u$ into the kernel of $A$ with respect to $F''(w)$, i.e. $(y(u),p(u))$ solves (6.4). Then for every $y\in Y$,
--   $$\|p(u)\|_w\;\le\;\|u-A^*y\|^*_w , \tag{6.6}$$
--   and this inequality is an equality only when $y$ is an exact minimizer of the right-hand side, i.e. only if $\|u-A^*y\|^*_w\le\|u-A^*y'\|^*_w$ for every $y'\in Y$.
--
--   Any dual estimate $y$ thus yields a computable upper bound on the norm of the projection; in §9 this gives (9.2), $\pi(\tau,x)\le\|F'(x)+\tau c-A^*y\|^*_x$.
--
--   **Formalization Note** The page writes "For any $a\in Y$" but uses $y$ in (6.6); the quantified variable is the one in (6.6), and it is distinct from the multiplier $y(u)$ of the projection system. Surjectivity of $A$ is the standing assumption (6.1). The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 23–24, Proposition 6.3, (6.6)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Proposition 6.3** (pp. 23–24), (6.6). If `p = p(u)` is the projection of `u` into `ker A`
with respect to `F''(w)` (system (6.4), `w ∈ int K`), then for every `y' ∈ Y`,
`‖p(u)‖_w ≤ ‖u − A*y'‖*_w`; and the inequality is an equality only when `y'` is an exact
minimizer of the right-hand side. -/
theorem proposition_6_3 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : SelfScaledLongStep.PrimalDual.IsProjection F A w u y p) :
    (∀ y' : EuclideanSpace ℝ (Fin m),
        lnorm F w p ≤ dnorm F w (u - ContinuousLinearMap.adjoint A y')) ∧
      (∀ y' : EuclideanSpace ℝ (Fin m),
        lnorm F w p = dnorm F w (u - ContinuousLinearMap.adjoint A y') →
          ∀ y'' : EuclideanSpace ℝ (Fin m),
            dnorm F w (u - ContinuousLinearMap.adjoint A y') ≤
              dnorm F w (u - ContinuousLinearMap.adjoint A y'')) := by sorry

end SelfScaledLongStep.PathFollow
