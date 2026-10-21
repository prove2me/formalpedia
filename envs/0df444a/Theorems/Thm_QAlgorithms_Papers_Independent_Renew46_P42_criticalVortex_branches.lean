-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_criticalVortex_branches
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.criticalVortex_branches
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:35:47.691633+00:00
-- url     : https://prove2.me/theorems/7c629584-fb37-488c-b7e2-ded1d8558595
-- title:
--   All critical cubic roots and the physical branch
-- statement:
--   Let $c>0$ and $n>1$. Define $P_n(\xi)=(n^2-1)\xi^3+n\xi^2-2n^2\xi+n$ and
--
--   $$\beta=\arccos\!\left[-\frac{27-70n^2+45n^4}{2n^2(6n^2-5)^{3/2}}\right],\quad u_i=\frac{2nc\sqrt{6n^2-5}\cos([2\pi(i-1)+\beta]/3)-nc}{3(n^2-1)},\quad i=1,2,3.$$
--
--   All three $u_i/c$ are roots, and every real root is one of them. Their physical selection and monotonicity are
--
--   $$u_1>c,\qquad u_2<0,\qquad0<u_3<c,\qquad n\longmapsto u_3(n)\text{ is strictly decreasing on }(1,\infty).$$
--
--   Thus $u_3$ is the unique root speed in $[0,c)$. For the constructed relativistic vortex, any $W,r>0$ with $nu(r)\ne c$ satisfies $l_-'(r)=0$ exactly when $P_n(u(r)/c)=0$.
--
--   This selects the algebraic critical branch without assuming a desired cubic root or certifying a causal event horizon. The endpoint $n=1$ is treated in the separate limits statement.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 10, §IV D, (94)–(96): critical cubic, explicit roots, physical branch

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.10–11, (94)–(96): all three explicit roots, unique physical branch,
and its monotone decrease. n=1 is handled by limits, never by evaluating (95). -/
theorem criticalVortex_branches (c : ℝ) (hc : 0 < c) :
    (∀ n : ℝ, 1 < n →
      (∀ i : Fin 3, criticalCubic n (criticalSpeed c n i / c) = 0) ∧
      (∀ xi : ℝ, criticalCubic n xi = 0 ↔ ∃ i : Fin 3, xi = criticalSpeed c n i / c) ∧
      c < criticalSpeed c n 0 ∧ criticalSpeed c n 1 < 0 ∧
      0 < criticalSpeed c n 2 ∧ criticalSpeed c n 2 < c ∧
      (∀ v : ℝ, (criticalCubic n (v / c) = 0 ∧ 0 ≤ v ∧ v < c) ↔
        v = criticalSpeed c n 2)) ∧
    StrictAntiOn (fun n => criticalSpeed c n 2) (Ioi 1) ∧
    (∀ (n W r : ℝ), 1 < n → 0 < W → 0 < r →
      n * vortexSpeed c W r ≠ c →
      (deriv (turningBranch c n (vortexSpeed c W) (-1)) r = 0 ↔
        criticalCubic n (vortexSpeed c W r / c) = 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
