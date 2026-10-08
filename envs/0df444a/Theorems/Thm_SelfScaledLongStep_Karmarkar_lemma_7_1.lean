-- Prove2me | Theorems.Thm_SelfScaledLongStep_Karmarkar_lemma_7_1
-- name    : SelfScaledLongStep.Karmarkar.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:40.042982+00:00
-- url     : https://prove2.me/theorems/4804d437-e05a-4c01-9eec-53d1abeaf0ef
-- title:
--   Lemma 7.1, p. 27 — the updated lower bound satisfies ζ⁺ ≤ ζ∗ and ⟨c, x̂⟩ − ζ⁺ ≤ νσ_x̂(−p)
-- statement:
--   Let $K\subseteq E=\mathbb R^n$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$ ($\nu\ge1$). Consider the problem
--   $$(P)\qquad \min\ \langle c,x\rangle\quad\text{s.t.}\quad Bx=0,\ \langle d,x\rangle=1,\ x\in K,$$
--   with $B:E\to\mathbb R^m$ linear and surjective and $d\in K^*$, and assume that the dual
--   $$(D)\qquad \max\ \zeta\quad\text{s.t.}\quad B^*y+d\zeta+s=c,\ s\in K^*$$
--   has a strictly feasible solution ($s\in\operatorname{int}K^*$) and that $\langle c,\cdot\rangle$ is not constant on the feasible set of (P). Let $\zeta^*$ be the optimal value of (P).
--
--   Let $\hat x$ be strictly feasible for (P) and let $\hat\zeta\le\zeta^*$. Let $p(c)$ and $p(d)$ be the projections of $\hat c$ and $\hat d$ into $\ker B$ with respect to $F''(\hat x)$, i.e. $Bp(u)=0$, $B^*y(u)+F''(\hat x)p(u)=\hat u$ (7.3). Let $\zeta^+$ be the possibly updated lower bound: $\zeta^+=\hat\zeta$ if $\tilde x(\hat\zeta)\notin\operatorname{int}K$, and $\zeta^+=\hat\zeta+1/\sigma_{\tilde x(\hat\zeta)}(p(d)+\hat x/\nu)$ otherwise (7.6). Let $p=p(c)-\zeta^+p(d)$ (7.5). Then $\zeta^+\le\zeta^*$ and
--   $$\langle c,\hat x\rangle-\zeta^+\le\nu\,\sigma_{\hat x}(-p).\qquad(7.7)$$
--
--   The lemma says that the lower-bound update never overshoots the optimal value, and that the resulting gap is controlled by how far one can move from $\hat x$ along $p$ before leaving $K$. It generalizes a result of Anstreicher for linear programming, and is the bound used in the third line of the potential estimate (7.10).
--
--   **Formalization Note** $\sigma_x(p)=\min\{\beta\ge0:\beta x-p\in K\}$ is `sigma K x p`. The vectors $\hat c$, $\hat d$ are $c+\frac{\langle c,\hat x\rangle}{\nu}F'(\hat x)$, $d+\frac{\langle d,\hat x\rangle}{\nu}F'(\hat x)$ (the page prints "$-$", a misprint; see the definitions item). The projections are taken as data $(y(c),p(c))$, $(y(d),p(d))$ satisfying (7.3); they are unique by Proposition 6.1. $E^*$ is identified with $E$; the barrier's Hessian is assumed nondegenerate (implied for a pointed cone); the conjugate barrier is a supremum over $\operatorname{int}K$. Strict feasibility of (P) is implied by $\hat x$; strict feasibility of (D) is assumption (6.3) of §6 and makes $\zeta^*$ finite. The hypothesis $\nu\ge1$ is a consequence of pointedness stated on p. 3, taken as a binder.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 27, Lemma 7.1, (7.7); standing assumptions (6.1)–(6.3), §7 p. 25

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_Karmarkar_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.Karmarkar

/-- **Lemma 7.1** (p. 27). Let `x̂ ∈ S⁰(P)` and `ζ̂ ≤ ζ*`, let `p(c)`, `p(d)` solve (7.3) for
`û = ĉ`, `û = d̂`, let `ζ⁺` be the possibly updated lower bound (7.6) and `p = p(c) − ζ⁺p(d)`
(7.5). Then `ζ⁺ ≤ ζ*` and (7.7) `⟨c, x̂⟩ − ζ⁺ ≤ ν σ_x̂(−p)`. -/
theorem lemma_7_1
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
    ζp ≤ zetaStar K B c d ∧ ⟪c, xh⟫_ℝ - ζp ≤ ν * sigma K xh (-p) := by sorry

end SelfScaledLongStep.Karmarkar
