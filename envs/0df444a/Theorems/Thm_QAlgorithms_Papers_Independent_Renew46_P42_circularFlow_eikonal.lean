-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_circularFlow_eikonal
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.circularFlow_eikonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:32:33.823218+00:00
-- url     : https://prove2.me/theorems/817fdc02-aa69-4da0-9a45-3f441b47acb1
-- title:
--   Separated real eikonals for circular flow
-- statement:
--   Let $c>0$, constant $n\ge1$, $\omega\ne0$, and real angular momentum $l$. Let $u(r)$ be $C^1$ and $|u(r)|<c$ on an open radial interval $J\subset(0,\infty)$. Put
--
--   $$F(r,l)=1-\frac{l^2}{r^2}+\frac{n^2-1}{1-u(r)^2/c^2}\left(1-\frac{u(r)l}{cr}\right)^2.$$
--
--   For a differentiable radial function $R$, the separated phase $S=(\omega/c)[-ct+l\phi+R(r)]$ solves the massless Hamilton–Jacobi symbol (75) exactly when $R'(r)^2=F(r,l)$. If $F\ge0$ throughout $J$, $r_b\in J$ and $\sigma\in\{1,-1\}$, construct
--
--   $$S(t,r,\phi)=\frac\omega c\left[-ct+l\phi+\sigma\int_{r_b}^r\sqrt{F(s,l)}\,ds\right].$$
--
--   This phase is differentiable and solves (75) locally on the angular coordinate patch. If $F(r,l)<0$, there is no real number whose square is $F(r,l)$.
--
--   This supplies the radial quadratures without asserting completeness of general wave solutions or continuation across forbidden regions.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 8, §IV C, (75)–(77): separated eikonal for circular flow

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.8, (75)–(77): actual separated radial quadratures solve the massless
Hamilton–Jacobi equation on an allowed open radial interval. -/
theorem circularFlow_eikonal (c n omega l sigma rBase : ℝ)
    (u : ℝ → ℝ) (J : Set ℝ) (z : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (ho : omega ≠ 0)
    (hsigma : sigma = 1 ∨ sigma = -1) (hJ : IsOpen J) (hconv : Convex ℝ J)
    (hbase : rBase ∈ J) (hz : z 1 ∈ J) (hreg : ContDiffOn ℝ 1 u J)
    (hpositive : ∀ r ∈ J, 0 < r)
    (hsub : ∀ r ∈ J, |u r| < c)
    (hallowed : ∀ r ∈ J, 0 ≤ radialF c n u r l) :
    (∀ R : ℝ → ℝ, DifferentiableAt ℝ R (z 1) →
      (cylindricalSymbol c n u (separatedPhase c omega l R) z = 0 ↔
        (deriv R (z 1)) ^ 2 = radialF c n u (z 1) l)) ∧
    DifferentiableAt ℝ (circularEikonal c n omega l sigma rBase u) z ∧
    cylindricalSymbol c n u (circularEikonal c n omega l sigma rBase u) z = 0 ∧
    (∀ r : ℝ, radialF c n u r l < 0 → ¬∃ a : ℝ, a ^ 2 = radialF c n u r l) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
