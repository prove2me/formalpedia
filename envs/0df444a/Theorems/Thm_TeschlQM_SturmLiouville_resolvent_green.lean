-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_resolvent_green
-- name    : TeschlQM.SturmLiouville.resolvent_green
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:48:59.925027+00:00
-- url     : https://prove2.me/theorems/81cea16c-7c55-439a-9b33-cac5943b3473
-- title:
--   Lemma 9.7 — the resolvent as an integral operator with Green function
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data, let $v, w$ be as in Theorem 9.6, and let $A$ be the self-adjoint operator of Theorem 9.6. Suppose $z \in \rho(A)$. Then there is a solution $u_a(z,x)$ of $(\tau - z)u = 0$ which is in $L^2((a,c), r\,dx)$ and satisfies the boundary condition $W_a(v, u_a) = 0$ at $a$ if $\tau$ is l.c. at $a$; similarly there is a solution $u_b(z, x)$ with the analogous properties near $b$. Their Wronskian $W(u_b(z), u_a(z))$ is a nonzero constant, and for all $g \in L^2(I, r\,dx)$
--   $$(A - z)^{-1} g(x) = \int_a^b G(z, x, y) g(y) r(y)\,dy, \qquad G(z,x,y) = \frac{1}{W(u_b(z), u_a(z))}\begin{cases} u_b(z,x) u_a(z,y), & x \ge y,\\ u_a(z,x) u_b(z,y), & x \le y.\end{cases}$$
--
--   The Green function is the basic tool for the spectral analysis of Sturm–Liouville operators, and its solutions $u_a$, $u_b$ are used in the proof of Weyl's alternative.
--
--   **Formalization Note.** The lemma as printed says "a solution $u_a(z,x)$ of $(\tau - z)u = g$"; the proof and (9.28) require $(\tau - z) u = 0$, which is what is stated. The boundary condition is stated as $W_x(v, u_a) \to 0$ as $x \to a$. The resolvent is a bounded $R$ with `IsResolventAt A z R`, and the identity holds for almost every $x$, with the integrand integrable for almost every $x$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 188, Lemma 9.7, Eqs. (9.27)–(9.28)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_operatorGraph
import Definitions.Def_TeschlQM_SturmLiouville_IsResolventAt
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear

namespace TeschlQM.SturmLiouville

open MeasureTheory Filter Topology

/-- Teschl, Lemma 9.7, p. 188. Let `A` be the self-adjoint operator of Theorem 9.6 (graph (9.19),
domain (9.20)) and `z ∈ ρ(A)` with resolvent `R = (A − z)⁻¹`. Then there is a solution `u_a` of
`(τ − z) u = 0` that is in `L²((a, c), r dx)` and satisfies the boundary condition at `a`
(`W_a(v, u_a) = 0`) if `τ` is l.c. at `a`, and similarly `u_b` near `b`; `W(u_b, u_a)` is a nonzero
constant, and `(A − z)⁻¹ g (x) = ∫_a^b G(z, x, y) g(y) r(y) dy` (9.27) with the Green function (9.28).
The printed equation "`(τ − z) u = g`" in the lemma is read as `(τ − z) u = 0`, as the proof and
(9.28) require. The integral is `∫ … ∂(r dx)` over `I`; its integrand is stated to be integrable. -/
theorem resolvent_green (L : SLData) (v w : ℝ → ℂ)
    (hv : IsLimitCircleLeft L → InMaxDomain L v ∧
      wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0)
    (hw : IsLimitCircleRight L → InMaxDomain L w ∧
      wronskianRight L (fun x => starRingEnd ℂ (w x)) w = 0 ∧
      ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L w f ≠ 0)
    (A : Lp ℂ 2 L.measure →ₗ.[ℂ] Lp ℂ 2 L.measure)
    (hA : (A.graph : Set (Lp ℂ 2 L.measure × Lp ℂ 2 L.measure)) =
      operatorGraph L (bcDomain L v w))
    (z : ℂ) (R : Lp ℂ 2 L.measure →L[ℂ] Lp ℂ 2 L.measure) (hR : IsResolventAt A z R) :
    ∃ ua ub : ℝ → ℂ,
      IsSolution L z 0 ua ∧ IsSqIntegrableNearLeft L ua ∧
        (IsLimitCircleLeft L → Tendsto (fun x => wronskian L x v ua) L.atLeft (𝓝 0)) ∧
      IsSolution L z 0 ub ∧ IsSqIntegrableNearRight L ub ∧
        (IsLimitCircleRight L → Tendsto (fun x => wronskian L x w ub) L.atRight (𝓝 0)) ∧
      ∃ W₀ : ℂ, W₀ ≠ 0 ∧ (∀ x ∈ L.I, wronskian L x ub ua = W₀) ∧
        ∀ g : Lp ℂ 2 L.measure,
          (∀ᵐ x ∂L.measure, Integrable
            (fun y => (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y) L.measure) ∧
          (R g : ℝ → ℂ) =ᵐ[L.measure]
            fun x => ∫ y, (if y ≤ x then ub x * ua y else ua x * ub y) / W₀ * g y ∂L.measure := by sorry

end TeschlQM.SturmLiouville
