-- Prove2me | Theorems.Thm_SelfScaledLongStep_Karmarkar_eq_7_8
-- name    : SelfScaledLongStep.Karmarkar.eq_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:51.602975+00:00
-- url     : https://prove2.me/theorems/56761daa-0ff9-4fe3-83f0-99775a92b2b2
-- title:
--   (7.8), p. 28 — ‖p‖²_x̂ = ⟨c − ζ⁺d, p⟩
-- statement:
--   Let $K\subseteq E=\mathbb R^n$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$ ($\nu\ge1$), and let $B$, $c$, $d$ be the data of the Karmarkar-form problem
--   $$\min\ \langle c,x\rangle\quad\text{s.t.}\quad Bx=0,\ \langle d,x\rangle=1,\ x\in K,$$
--   under the standing assumptions of §7 ($B$ surjective, $d\in K^*$, a strictly feasible dual solution, a nonconstant objective on the feasible set). Let $\hat x$ be strictly feasible, and let $p(c)$, $p(d)$ be the projections of
--   $$\hat c=c+\frac{\langle c,\hat x\rangle}{\nu}F'(\hat x),\qquad \hat d=d+\frac{\langle d,\hat x\rangle}{\nu}F'(\hat x)$$
--   into $\ker B$ with respect to $F''(\hat x)$, i.e. $Bp(u)=0$, $B^*y(u)+F''(\hat x)p(u)=\hat u$ (7.3). Then for every real $\zeta$ the direction $p=p(c)-\zeta p(d)$ satisfies
--   $$\|p\|_{\hat x}^2=\langle c-\zeta d,p\rangle,\qquad(7.8)$$
--   where $\|p\|_{\hat x}=\langle F''(\hat x)p,p\rangle^{1/2}$ is the local norm.
--
--   The paper uses (7.8) with $\zeta=\zeta^+$, the updated lower bound, to rewrite the linear term of the potential change in (7.10).
--
--   **Formalization Note** The page states (7.8) for $\zeta=\zeta^+$; the statement here holds for every real $\zeta$, which contains the page's case (the page's derivation does not use any property of $\zeta^+$). The sign of $\hat c$, $\hat d$ corrects a misprint on p. 27 (see the definitions item); with the printed sign the identity is false. $\|p\|_{\hat x}$ is `lnorm F xh p`. $E^*$ is identified with $E$; nondegeneracy of $F''$ and the conjugate as a supremum over $\operatorname{int}K$ are inherited from the published setting. The standing assumptions of §7 are carried for uniformity with the other items; $\nu\ge1$ is a consequence of pointedness (p. 3), taken as a binder.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 28, (7.8); stated for every ζ in place of ζ⁺

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_Karmarkar_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.Karmarkar

/-- **(7.8)** (p. 28). For `x̂ ∈ S⁰(P)`, the projections `p(c)`, `p(d)` of `ĉ`, `d̂` by (7.3),
and any real `ζ` (the page uses `ζ = ζ⁺`), the direction `p = p(c) − ζ p(d)` satisfies
`‖p‖²_x̂ = ⟨c − ζ d, p⟩`. -/
theorem eq_7_8
    {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hB : Function.Surjective B)
    (c d : EuclideanSpace ℝ (Fin n)) (hd : d ∈ ConvexOptimization.dualCone K)
    (hD : ∃ (y : EuclideanSpace ℝ (Fin m)) (ζ : ℝ) (s : EuclideanSpace ℝ (Fin n)),
      s ∈ interior (ConvexOptimization.dualCone K) ∧
        ContinuousLinearMap.adjoint B y + ζ • d + s = c)
    (hnc : ∃ x₁ x₂ : EuclideanSpace ℝ (Fin n),
      KarFeasible K B d x₁ ∧ KarFeasible K B d x₂ ∧ ⟪c, x₁⟫_ℝ ≠ ⟪c, x₂⟫_ℝ)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : KarStrict K B d xh)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F B xh (cHat F ν c xh) yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F B xh (dHat F ν d xh) yd pd)
    (ζ : ℝ) :
    (lnorm F xh (karDir pc pd ζ)) ^ 2 = ⟪c - ζ • d, karDir pc pd ζ⟫_ℝ := by sorry

end SelfScaledLongStep.Karmarkar
