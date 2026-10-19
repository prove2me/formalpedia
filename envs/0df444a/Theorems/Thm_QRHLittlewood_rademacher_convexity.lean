-- Prove2me | Theorems.Thm_QRHLittlewood_rademacher_convexity
-- name    : QRHLittlewood.rademacher_convexity
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:35:18.214181+00:00
-- url     : https://prove2.me/theorems/874731b0-c5ab-493e-b185-d2740a45a8ce
-- title:
--   Rademacher's convexity bound for primitive Dirichlet $L$-functions
-- statement:
--   Let $\chi$ be a primitive Dirichlet character modulo $q\ge3$ and let $s$ be a complex number with $-\tfrac12\le\Re s\le\tfrac32$. Then
--
--   $$|L(s,\chi)|\ \le\ \zeta\big(\tfrac32\big)\left(\frac{q\,|1+s|}{2\pi}\right)^{(3/2-\Re s)/2}.$$
--
--   It interpolates between the trivial bound $|L(s,\chi)|\le\zeta(3/2)$ on $\Re s=3/2$ and the bound on $\Re s=-1/2$ given by the functional equation.
-- source:
--   H. Rademacher, On the Phragmén–Lindelöf theorem and some applications, Math. Z. 72 (1959/60), 192–204 (exponent 1/2 case); as stated and used in B. W. Daugherty, S. Ryan, G. Ward, Certified harmonic-measure barriers and explicit Littlewood bounds from zero-free regions, https://doi.org/10.5281/zenodo.23400116, Section 6, "The Dirichlet inputs".

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Real

namespace QRHLittlewood

theorem rademacher_convexity (q : ℕ) [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (s : ℂ) (hs1 : -1 / 2 ≤ s.re) (hs2 : s.re ≤ 3 / 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (riemannZeta (3 / 2)).re * ((q : ℝ) * ‖1 + s‖ / (2 * π)) ^ ((3 / 2 - s.re) / 2) := by sorry

end QRHLittlewood
