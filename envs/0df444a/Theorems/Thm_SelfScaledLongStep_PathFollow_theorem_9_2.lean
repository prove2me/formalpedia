-- Prove2me | Theorems.Thm_SelfScaledLongStep_PathFollow_theorem_9_2
-- name    : SelfScaledLongStep.PathFollow.theorem_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:46.80814+00:00
-- url     : https://prove2.me/theorems/fc0d1dd3-6990-4baa-b5d5-8640e00c4a74
-- title:
--   Theorem 9.2, p. 39 — a full Newton step from π(τ, x) < 1 gives π(τ, x₊) ≤ |p|_x π(τ, x) ≤ π²(τ, x)
-- statement:
--   Throughout, $K\subset E=\mathbb R^n$ is a closed convex pointed cone with nonempty interior and $F$ is a $\nu$-self-scaled barrier for $K$ (Definition 2.1). The problem data of §6 are a surjective linear map $A:E\to Y=\mathbb R^m$ (6.1), $b\in Y$ and $c\in E^*$, with a strictly feasible dual point (6.3); $S^0(P)=\{x\in\operatorname{int}K: Ax=b\}$. Fix $\tau>0$ and $x\in S^0(P)$, and let $p=p(\tau,x)$ be the Newton direction, i.e. $(y,p)$ solves
--   $$\tau c+F'(x)-F''(x)p-A^*y=0,\qquad Ap=0 .$$
--   Let $\pi(\tau,x)=\|p\|_x<1$ and take the full Newton step $x_+=x-p$. Then $x_+\in S^0(P)$, and the Newton direction $p_+=p(\tau,x_+)$ at the new point satisfies
--   $$\pi(\tau,x_+)=\|p_+\|_{x_+}\;\le\;|p|_x\,\pi(\tau,x)\;\le\;\pi^2(\tau,x).$$
--
--   The region $\pi(\tau,x)<1$ is therefore a region of quadratic convergence of Newton's method with unit step for the penalty function $\psi(\tau,\cdot)$.
--
--   **Formalization Note** The page states the theorem for the whole Newton sequence started from $\pi(\tau,x_0)<1$ (printed as "$\tau(\tau,x_0)<1$", a typo for $\pi$); the statement here is one iteration, and the sequence form follows by induction because $\pi(\tau,x_{k+1})\le\pi^2(\tau,x_k)<1$. That $x_+\in S^0(P)$ is not printed as a claim but is presupposed by $\pi(\tau,x_+)$; it is stated as a conclusion. The bound holds for every solution $(y_+,p_+)$ of the Newton system at $x_+$. The standing assumptions (6.1)–(6.3) of §9 (p. 38) are hypotheses. The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 39, Theorem 9.2 (with (9.2))

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Theorem 9.2** (p. 39), one full Newton step (`α = 1`). Let `x ∈ S⁰(P)`, `τ > 0`, and let
`p = p(τ, x)` be the Newton direction with `π(τ, x) = ‖p‖_x < 1`. Then `x₊ = x − p ∈ S⁰(P)`, and
for the Newton direction `p₊ = p(τ, x₊)` at the new point,
`π(τ, x₊) = ‖p₊‖_{x₊} ≤ |p|_x π(τ, x) ≤ π²(τ, x)`. -/
theorem theorem_9_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n)), IsDualStrict K A c y s)
    (τ : ℝ) (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) (hx : IsPrimalStrict K A b x)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : IsNewtonDir F A c τ x y p) (hπ : lnorm F x p < 1) :
    IsPrimalStrict K A b (x - p) ∧
      ∀ (y' : EuclideanSpace ℝ (Fin m)) (p' : EuclideanSpace ℝ (Fin n)),
        IsNewtonDir F A c τ (x - p) y' p' →
          lnorm F (x - p) p' ≤ absn K x p * lnorm F x p ∧
            absn K x p * lnorm F x p ≤ (lnorm F x p) ^ 2 := by sorry

end SelfScaledLongStep.PathFollow
