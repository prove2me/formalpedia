-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_8_2
-- name    : SelfScaledLongStep.PrimalDual.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:11.39841+00:00
-- url     : https://prove2.me/theorems/a1579194-b508-4c22-a48d-bd2b80460302
-- title:
--   Theorem 8.2, p. 35 — one joint-scaling primal-dual step lowers φ(x, s) by at least √3/2 − ln(1 + √3/2)
-- statement:
--   Consider the conic problem $\min\{\langle c,x\rangle: Ax=b,\ x\in K\}$ and its dual $\max\{\langle b,y\rangle: A^*y+s=c,\ s\in K^*\}$, where $K$ is a self-scaled cone with a $\nu$-self-scaled barrier $F$, $F_*$ is the conjugate barrier, and $A$ is surjective (6.1). Fix $\rho\ge\sqrt\nu$ and the potential
--   $$\phi(x,s)=(\nu+\rho)\ln\langle s,x\rangle+F(x)+F_*(s).$$
--   Let $x$ be strictly feasible for the primal ($x\in\operatorname{int}K$, $Ax=b$) and $(y,s)$ strictly feasible for the dual ($s\in\operatorname{int}K^*$, $A^*y+s=c$). One iteration of the joint-scaling method of §8 is:
--
--   1. (a) take the scaling point $w\in\operatorname{int}K$ with $s=F''(w)x$ and put $\sigma=\sigma_x(w)$;
--   2. (b) solve (8.1): $F''(w)\Delta x+\Delta s=\frac{\nu+\rho}{\langle s,x\rangle}s+F'(x)$, $A\Delta x=0$, $A^*\Delta y+\Delta s=0$;
--   3. (c) put $\bar\sigma=\max\{\sigma_x(\Delta x),\sigma^*_s(\Delta s)\}$, $\bar\alpha=1/(\sigma^2+\bar\sigma)$, and accept any step size $\alpha$ with $\phi(x-\alpha\Delta x,s-\alpha\Delta s)\le\phi(x-\bar\alpha\Delta x,s-\bar\alpha\Delta s)$;
--   4. (d) set $x_+=x-\alpha\Delta x$, $s_+=s-\alpha\Delta s$, $y_+=y-\alpha\Delta y$.
--
--   Then:
--
--   1. the initial step is admissible and already achieves the decrease: $x-\bar\alpha\Delta x\in\operatorname{int}K$, $s-\bar\alpha\Delta s\in\operatorname{int}K^*$, and
--   $$\phi(x-\bar\alpha\Delta x,s-\bar\alpha\Delta s)\le\phi(x,s)-\frac{\sqrt3}{2}+\ln\Big(1+\frac{\sqrt3}{2}\Big);$$
--   2. for every step size $\alpha$ accepted in (c) with $x_+\in\operatorname{int}K$ and $s_+\in\operatorname{int}K^*$, the new iterate is strictly feasible ($Ax_+=b$, $A^*y_++s_+=c$) and
--   $$\phi(x_+,s_+)\le\phi(x,s)-\frac{\sqrt3}{2}+\ln\Big(1+\frac{\sqrt3}{2}\Big).$$
--
--   A constant decrease of $\phi$ per iteration gives, through Theorem 8.1, a long-step primal-dual method with an $O(\sqrt\nu\ln(1/\epsilon))$ iteration bound when $\rho=\gamma\sqrt\nu$.
--
--   **Formalization Note** The theorem is stated for one iteration from an arbitrary strictly feasible pair; the index $k$ of the page plays no role. The scaling point and the displacement are binders satisfying their defining equations (`IsScalingPoint`, `IsJointScalingDir`); their existence is Theorem 3.2 and Proposition 6.1. Part 1 makes explicit what step (c)–(d) presupposes: without it the bound for accepted steps could hold vacuously, because the conjugate barrier and the logarithm take junk values outside $\operatorname{int}K^*$ and $(0,\infty)$. The strict feasibility of the new iterate in part 2 is immediate from (8.1) and is included for completeness. $\sigma^*_s(\Delta s)$ is `sigma (dualCone K) s ds` (centre $s$ in $K^*$). $E^*\cong E=\mathbb R^n$, $Y\cong\mathbb R^m$; the barrier is nondegenerate as in the published setting; `conj K F` is a supremum over $\operatorname{int}K$ evaluated only at points of $\operatorname{int}K^*$; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 35, Theorem 8.2; algorithm of §8, pp. 33–35, (8.1)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PrimalDual_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Theorem 8.2** (p. 35), one iteration of the joint-scaling primal-dual method of §8.
Data: (6.1) `A` surjective; `x ∈ S⁰(P)`, `(y, s) ∈ S⁰(D)`; `ρ ≥ √ν`; the scaling point `w`
(`s = F''(w)x`, step (a)); the displacement `(Δx, Δy, Δs)` solving (8.1) (step (b));
`ᾱ = 1/(σ_x(w)² + max{σ_x(Δx), σ*_s(Δs)})` (step (c)); `φ(x, s) = (ν + ρ) ln⟨s, x⟩ + F(x) + F*(s)`.
Conclusion: (1) the ᾱ-step stays strictly inside `K × K*` and lowers `φ` by at least
`√3/2 − ln(1 + √3/2)`; (2) every step size `α` accepted by rule (c) (strictly interior and
`φ` at `α` no larger than at `ᾱ`) gives a strictly feasible new iterate (step (d)) whose
potential satisfies the same bound. -/
theorem theorem_8_2 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hx : IsPrimalStrict K A b x) (hys : IsDualStrict K A c y s)
    (ρ : ℝ) (hρ : Real.sqrt ν ≤ ρ)
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsScalingPoint K F x s w)
    (dx : EuclideanSpace ℝ (Fin n)) (dy : EuclideanSpace ℝ (Fin m)) (ds : EuclideanSpace ℝ (Fin n))
    (hdir : IsJointScalingDir F A ν ρ x s w dx dy ds) :
    (x - alphaBar K x s w dx ds • dx ∈ interior K ∧
      s - alphaBar K x s w dx ds • ds ∈ interior (ConvexOptimization.dualCone K) ∧
      pdPotential K F ν ρ (x - alphaBar K x s w dx ds • dx) (s - alphaBar K x s w dx ds • ds) ≤
        pdPotential K F ν ρ x s - Real.sqrt 3 / 2 + Real.log (1 + Real.sqrt 3 / 2)) ∧
    ∀ α : ℝ, x - α • dx ∈ interior K → s - α • ds ∈ interior (ConvexOptimization.dualCone K) →
      pdPotential K F ν ρ (x - α • dx) (s - α • ds) ≤
        pdPotential K F ν ρ (x - alphaBar K x s w dx ds • dx)
          (s - alphaBar K x s w dx ds • ds) →
      IsPrimalStrict K A b (x - α • dx) ∧ IsDualStrict K A c (y - α • dy) (s - α • ds) ∧
        pdPotential K F ν ρ (x - α • dx) (s - α • ds) ≤
          pdPotential K F ν ρ x s - Real.sqrt 3 / 2 + Real.log (1 + Real.sqrt 3 / 2) := by sorry

end SelfScaledLongStep.PrimalDual
