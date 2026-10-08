-- Prove2me | Theorems.Thm_SelfScaledLongStep_PathFollow_corollary_4_1_iii
-- name    : SelfScaledLongStep.PathFollow.corollary_4_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:20.052889+00:00
-- url     : https://prove2.me/theorems/8983b551-bc73-4502-9e71-ad8b9b16f041
-- title:
--   Corollary 4.1 (iii), p. 16 — (1/σ_x(v))F″(x) ≤ F″(w) ≤ σ_v(x)F″(x) when F′(v) = −F″(w)x
-- statement:
--   Throughout, $K\subset E=\mathbb R^n$ is a closed convex pointed cone with nonempty interior and $F$ is a $\nu$-self-scaled barrier for $K$ (Definition 2.1). Let $x,v\in\operatorname{int}K$ and let $w\in\operatorname{int}K$ satisfy $F'(v)=-F''(w)x$. Then, in the order of positive semidefinite operators,
--   $$\frac{1}{\sigma_x(v)}F''(x)\;\le\;F''(w)\;\le\;\sigma_v(x)\,F''(x), \tag{4.7}$$
--   where $\sigma_x(v)=\min\{\beta\ge0:\beta x-v\in K\}$.
--
--   The inequality controls the Hessian at the intermediate point of Corollary 3.1 by the Hessian at $x$; it is used in the proof of Theorem 4.3.
--
--   **Formalization Note** The operator order "$A\le B$" is written through quadratic forms: for every $u\in E$, $\sigma_x(v)^{-1}\langle F''(x)u,u\rangle\le\langle F''(w)u,u\rangle\le\sigma_v(x)\langle F''(x)u,u\rangle$. Since $v\in\operatorname{int}K$ is nonzero and $K$ is pointed, $\sigma_x(v)>0$, so the division is genuine. Parts (i)–(ii) of Corollary 4.1 are not stated here. The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 16, Corollary 4.1 (iii), (4.7)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Corollary 4.1 (iii)** (p. 16), (4.7). For `x, v ∈ int K` and `w ∈ int K` with
`F'(v) = −F''(w)x`: `(1/σ_x(v)) F''(x) ≤ F''(w) ≤ σ_v(x) F''(x)`, the order being that of
positive semidefinite operators, written here through the quadratic forms `u ↦ ⟨F''(·)u, u⟩`. -/
theorem corollary_4_1_iii {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x v w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hv : v ∈ interior K)
    (hw : w ∈ interior K) (hwv : gradient F v = -(hess F w x)) :
    ∀ u : EuclideanSpace ℝ (Fin n),
      (1 / sigma K x v) * ⟪hess F x u, u⟫_ℝ ≤ ⟪hess F w u, u⟫_ℝ ∧
        ⟪hess F w u, u⟫_ℝ ≤ sigma K v x * ⟪hess F x u, u⟫_ℝ := by sorry

end SelfScaledLongStep.PathFollow
