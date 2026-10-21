-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_circularFlow_turningPoints
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.circularFlow_turningPoints
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:34:48.346416+00:00
-- url     : https://prove2.me/theorems/d8c8b9d1-60f9-4f63-a30f-d41c374c9c21
-- title:
--   Turning branches and the fixed-angular-momentum derivative criterion
-- statement:
--   Let $c>0$, $n>1$, $r>0$, and let the circular speed profile be differentiable at $r$, with $0\le u(r)<c$. The radial function (77) factors as
--
--   $$F(r,l)=\gamma^2\left[n^2\left(1-\frac{ul}{cr}\right)^2-\left(\frac uc-\frac lr\right)^2\right].$$
--
--   Its finite roots in $l$ are $l_+=r(nc+u)/(nu+c)$ and, when $nu\ne c$, $l_-=r(nc-u)/(nu-c)$. When $nu=c$ only the finite plus root remains. For $s=\pm1$ with $nu+sc\ne0$,
--
--   $$l_s'=\frac{l_s}{r}-\frac{(n^2-1)rcu'}{(nu+sc)^2},\qquad \left.\partial_rF(r,l)\right|_{l=l_s(r)}=\frac{2sn}{r}l_s'.$$
--
--   The partial derivative holds $l$ fixed before substitution. For the relativistic vortex with any $W>0$, $ru'=-u(1-u^2/c^2)$, $l_+>0$, and $l_+'>0$. If $nu<c$, then $l_-<0$; if $nu>c$, the minus root has negative fixed-$l$ radial derivative.
--
--   The derivative sign gives the local inner/outer turning criterion, without a global capture assertion.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 10, §IV D, (89)–(93): turning branches and inner/outer derivative criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.10, (89)–(93): finite turning branches and the fixed-l derivative.
Source correction: (92) prints ±2n*l'; differentiation of (77) requires
±2n*l'/r. The sign criterion is unchanged because r>0. The singular minus
chart at n*u=c is explicitly excluded and only the finite plus root remains. -/
theorem circularFlow_turningPoints (c n r : ℝ) (u : ℝ → ℝ)
    (hc : 0 < c) (hn : 1 < n) (hr : 0 < r)
    (hu0 : 0 ≤ u r) (hu : u r < c) (hreg : DifferentiableAt ℝ u r) :
    (∀ l : ℝ, radialF c n u r l =
      (1 / (1 - (u r) ^ 2 / c ^ 2)) *
        (n ^ 2 * (1 - u r * l / (c * r)) ^ 2 - (u r / c - l / r) ^ 2)) ∧
    (∀ l : ℝ, radialF c n u r l = 0 ↔
      l = turningBranch c n u 1 r ∨
        (n * u r ≠ c ∧ l = turningBranch c n u (-1) r)) ∧
    (∀ s : ℝ, (s = 1 ∨ s = -1) → n * u r + s * c ≠ 0 →
      deriv (turningBranch c n u s) r = turningBranch c n u s r / r -
        (n ^ 2 - 1) / (n * u r + s * c) ^ 2 * r * deriv u r * c ∧
      deriv (fun a => radialF c n u a (turningBranch c n u s r)) r =
        s * 2 * n / r * deriv (turningBranch c n u s) r) ∧
    (∀ W : ℝ, 0 < W →
      r * deriv (vortexSpeed c W) r =
        -vortexSpeed c W r * (1 - (vortexSpeed c W r) ^ 2 / c ^ 2) ∧
      0 < turningBranch c n (vortexSpeed c W) 1 r ∧
      0 < deriv (turningBranch c n (vortexSpeed c W) 1) r ∧
      (n * vortexSpeed c W r < c → turningBranch c n (vortexSpeed c W) (-1) r < 0) ∧
      (c < n * vortexSpeed c W r →
        deriv (fun a => radialF c n (vortexSpeed c W) a
          (turningBranch c n (vortexSpeed c W) (-1) r)) r < 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
