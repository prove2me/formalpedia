-- Prove2me | Theorems.Thm_SelfScaledLongStep_Karmarkar_theorem_7_2
-- name    : SelfScaledLongStep.Karmarkar.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:32.002548+00:00
-- url     : https://prove2.me/theorems/3c6470d5-75c1-4dcc-bcb3-29c259be0114
-- title:
--   Theorem 7.2, p. 28 — a long Karmarkar step lowers Φ by at least (‖p‖²_x̂/|p|²_x̂)(1 − ln 2) ≥ 1 − ln 2
-- statement:
--   Let $K\subseteq E=\mathbb R^n$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$ ($\nu\ge1$). Consider
--   $$(P)\qquad \min\ \langle c,x\rangle\quad\text{s.t.}\quad Bx=0,\ \langle d,x\rangle=1,\ x\in K,$$
--   with $B:E\to\mathbb R^m$ linear and surjective and $d\in K^*$; assume the dual $\max\{\zeta: B^*y+d\zeta+s=c,\ s\in K^*\}$ has a strictly feasible solution and that $\langle c,\cdot\rangle$ is not constant on the feasible set of (P). Let $\zeta^*$ be the optimal value of (P) and use the potential
--   $$\Phi(x;\zeta)=\nu\ln\langle c-\zeta d,x\rangle+F(x),\qquad x\in\operatorname{int}K,\ Bx=0.$$
--
--   Let $\hat x$ be strictly feasible, $\hat\zeta\le\zeta^*$, let $p(c)$, $p(d)$ be the projections (7.3) of $\hat c$, $\hat d$, let $\zeta^+$ be the possibly updated lower bound (7.6) and $p=p(c)-\zeta^+p(d)$ the search direction (7.5). Then there is $\alpha>0$ such that $x^+=\hat x-\alpha p$ lies in $\{x\in\operatorname{int}K: Bx=0\}$, $\langle c-\zeta^+d,x^+\rangle>0$, and
--   $$\Phi(x^+;\zeta^+)\le\Phi(\hat x;\hat\zeta)-\frac{\|p\|_{\hat x}^2}{|p|_{\hat x}^2}(1-\ln2)\le\Phi(\hat x;\hat\zeta)-(1-\ln2).\qquad(7.9)$$
--   Here $\|p\|_{\hat x}=\langle F''(\hat x)p,p\rangle^{1/2}$ and $|p|_{\hat x}=\max\{\sigma_{\hat x}(p),\sigma_{\hat x}(-p)\}$ with $\sigma_x(p)=\min\{\beta\ge0:\beta x-p\in K\}$.
--
--   This is the main result of the Karmarkar subsection: each long step reduces the potential by an absolute constant, which with Theorem 7.1 gives an $O(\nu\ln(1/\epsilon))$ iteration bound. The step may leave the normalization $\langle d,x\rangle=1$, but since $\Phi$ is homogeneous of degree $0$ the rescaled point $x^+/\langle d,x^+\rangle$ achieves the same reduction.
--
--   **Formalization Note** "For a suitable value of $\alpha$" is an existential with $\alpha>0$. The conjunct $\langle c-\zeta^+d,x^+\rangle>0$ is stated explicitly so that the logarithm in $\Phi(x^+;\zeta^+)$ is genuine; the page's claim that $x^+$ satisfies (7.9) presupposes it. The normalization $\langle d,x^+\rangle=1$ is not asserted, as on the page. $\zeta^+\le\zeta^*$ is the separate Lemma 7.1. The quotient $\|p\|^2/|p|^2$ is genuine because $p\neq0$ under the standing assumptions. The vectors $\hat c$, $\hat d$ use the sign "$+$", correcting a misprint on p. 27 (see the definitions item). Norms: $\|p\|_{\hat x}$ is `lnorm F xh p`, $|p|_{\hat x}$ is `absn K xh p`. $E^*$ is identified with $E$; nondegeneracy of $F''$ and the conjugate as a supremum over $\operatorname{int}K$ are inherited from the published setting; $\nu\ge1$ is a consequence of pointedness (p. 3), taken as a binder. Strict feasibility of (P) is implied by $\hat x$.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 28, Theorem 7.2, (7.9); standing assumptions (6.1)–(6.3), §7 p. 25

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_Karmarkar_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.Karmarkar

/-- **Theorem 7.2** (p. 28). With `x̂ ∈ S⁰(P)`, `ζ̂ ≤ ζ*`, the possibly updated lower bound `ζ⁺`
and the search direction `p = p(c) − ζ⁺p(d)` of (7.5), for a suitable `α` the point
`x⁺ = x̂ − αp` lies in `{x ∈ int K : Bx = 0}` and
(7.9) `Φ(x⁺; ζ⁺) ≤ Φ(x̂; ζ̂) − (‖p‖²_x̂/|p|²_x̂)(1 − ln 2) ≤ Φ(x̂; ζ̂) − (1 − ln 2)`.
The conjunct `0 < ⟨c − ζ⁺d, x⁺⟩` makes the logarithm in `Φ(x⁺; ζ⁺)` genuine. -/
theorem theorem_7_2
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
    (ζh : ℝ) (hζh : ζh ≤ zetaStar K B c d)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F B xh (cHat F ν c xh) yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F B xh (dHat F ν d xh) yd pd) :
    let ζp := zetaPlus K ν c d xh pc pd ζh
    let p := karDir pc pd ζp
    ∃ α : ℝ, 0 < α ∧ xh - α • p ∈ interior K ∧ B (xh - α • p) = 0 ∧
      0 < ⟪c - ζp • d, xh - α • p⟫_ℝ ∧
      karPotential F ν c d ζp (xh - α • p) ≤
        karPotential F ν c d ζh xh - (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ∧
      karPotential F ν c d ζh xh - (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ≤
        karPotential F ν c d ζh xh - (1 - Real.log 2) := by sorry

end SelfScaledLongStep.Karmarkar
