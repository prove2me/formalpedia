-- Prove2me | Theorems.Thm_SelfScaledLongStep_PathFollow_theorem_9_3
-- name    : SelfScaledLongStep.PathFollow.theorem_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:55.760221+00:00
-- url     : https://prove2.me/theorems/eb358563-aead-4c5a-9ff4-cb153a07f49f
-- title:
--   Theorem 9.3, p. 40 — the predictor-corrector step keeps π(τ, x) ≤ 1/4 and multiplies τ by at least 1 + 3/(8√ν + 2)
-- statement:
--   Throughout, $K\subset E=\mathbb R^n$ is a closed convex pointed cone with nonempty interior and $F$ is a $\nu$-self-scaled barrier for $K$ (Definition 2.1). The problem data of §6 are a surjective linear map $A:E\to Y=\mathbb R^m$ (6.1), $b\in Y$ and $c\in E^*$, with a strictly feasible dual point (6.3); $S^0(P)=\{x\in\operatorname{int}K: Ax=b\}$. Consider one iteration of the path-following scheme of p. 39. Let $\tau>0$ and $x\in S^0(P)$ with
--   $$\pi(\tau,x)=\|p(\tau,x)\|_x\le\tfrac14,$$
--   where $p(\tau,x)$ is the Newton direction ($\tau c+F'(x)-F''(x)p-A^*y=0$, $Ap=0$). Let $v=v(x)$ be the tangent direction, $c-F''(x)v-A^*\hat y=0$, $Av=0$, and assume $v\ne0$. Set
--   $$\Delta\tau=\frac{3}{8\sqrt{|v|_x\|v\|_x}},\qquad z=x-\Delta\tau\,v,\qquad \tau_+=\tau+\Delta\tau \quad\text{(predictor)},$$
--   $$x_+=z-p(\tau_+,z)\quad\text{(corrector)}.$$
--   Then $z\in\operatorname{int}K$, $x_+\in S^0(P)$, the condition (9.3) is preserved,
--   $$\pi(\tau_+,x_+)\le\tfrac14,$$
--   and (9.4) holds:
--   $$\tau_+\;\ge\;\Bigl(1+\frac{3}{8\sqrt\nu+2}\sqrt{\frac{\|v\|_x}{|v|_x}}\Bigr)\tau\;\ge\;\Bigl(1+\frac{3}{8\sqrt\nu+2}\Bigr)\tau .$$
--
--   Started from $\pi(\tau_0,x_0)\le1/4$, the scheme therefore stays in the region of quadratic convergence of Newton's method and increases the penalty parameter geometrically, by a factor at least $1+3/(8\sqrt\nu+2)$ per iteration, while allowing long steps $\Delta\tau$ when $\|v\|_x/|v|_x$ is large.
--
--   **Formalization Note** The theorem is stated for one iteration; (9.3) for all $k$ follows by induction from the initialization $\pi(\tau_0,x_0)\le1/4$. The hypothesis $v\ne0$ is an addition: for $v=0$ (when $c$ lies in the range of $A^*$, i.e. the objective is constant on the feasible set, which §7 excludes on p. 25) the step $\Delta\tau$ is undefined. The conclusions $z\in\operatorname{int}K$ and $x_+\in S^0(P)$ are presupposed by the scheme rather than printed as claims, and are stated explicitly. The predictor, the new parameter and the corrector are named data tied to the scheme by equations; the corrector's Newton system at $(\tau_+,z)$ and the bound $\pi(\tau_+,x_+)\le1/4$ hold for every solution of the respective Newton system. The standing assumptions (6.1)–(6.3) of §9 (p. 38) are hypotheses. The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 40, Theorem 9.3, (9.3)–(9.4); scheme on p. 39

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Theorem 9.3** (p. 40), one iteration of the predictor-corrector path-following scheme
(p. 39). Let `τ > 0`, `x ∈ S⁰(P)` with `π(τ, x) = ‖p(τ, x)‖_x ≤ 1/4`, and let `v = v(x) ≠ 0` be the
tangent direction. With `Δτ = 3/(8√(|v|_x‖v‖_x))`, the predictor `z = x − Δτ v`, `τ₁ = τ + Δτ`,
and the corrector `x₁ = z − p(τ₁, z)`:
* `z ∈ int K` and `x₁ ∈ S⁰(P)`;
* (9.3) is preserved: `π(τ₁, x₁) ≤ 1/4`;
* (9.4): `τ₁ ≥ (1 + (3/(8√ν + 2))√(‖v‖_x/|v|_x)) τ ≥ (1 + 3/(8√ν + 2)) τ`. -/
theorem theorem_9_3 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n)), IsDualStrict K A c y s)
    (τ : ℝ) (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) (hx : IsPrimalStrict K A b x)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : IsNewtonDir F A c τ x y p) (hπ : lnorm F x p ≤ 1 / 4)
    (ŷ : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n))
    (hvdir : IsTangentDir F A c x ŷ v) (hv : v ≠ 0)
    (Δτ τ₁ : ℝ) (z x₁ : EuclideanSpace ℝ (Fin n))
    (hΔτ : Δτ = tangentStep K F x v) (hz : z = x - Δτ • v) (hτ₁ : τ₁ = τ + Δτ)
    (yz : EuclideanSpace ℝ (Fin m)) (pz : EuclideanSpace ℝ (Fin n))
    (hpz : IsNewtonDir F A c τ₁ z yz pz) (hx₁ : x₁ = z - pz) :
    z ∈ interior K ∧ IsPrimalStrict K A b x₁ ∧
      (∀ (y' : EuclideanSpace ℝ (Fin m)) (p' : EuclideanSpace ℝ (Fin n)),
        IsNewtonDir F A c τ₁ x₁ y' p' → lnorm F x₁ p' ≤ 1 / 4) ∧
      (1 + 3 / (8 * Real.sqrt ν + 2) * Real.sqrt (lnorm F x v / absn K x v)) * τ ≤ τ₁ ∧
      (1 + 3 / (8 * Real.sqrt ν + 2)) * τ ≤
        (1 + 3 / (8 * Real.sqrt ν + 2) * Real.sqrt (lnorm F x v / absn K x v)) * τ := by sorry

end SelfScaledLongStep.PathFollow
