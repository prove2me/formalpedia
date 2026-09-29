-- Prove2me | Theorems.Thm_TateCurve_isRoot_prePsi_curve_pointX_laurentSeries
-- name    : TateCurve.isRoot_prePsi_curve_pointX_laurentSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/ced19498-f66c-5512-8973-c36cc5a837d2
-- title:
--   Division polynomial vanishes at Tate N-torsion abscissae
-- statement:
--   Let $F$ be a field of characteristic $0$, let $N$ be a nonzero natural number that is odd and satisfies $N \ge 5$, and let $\zeta \in F$ be a primitive $N$-th root of unity. Write $t =$ `HahnSeries.single 1 1` for the Hahn series with single coefficient $1$ in degree $1$, that is the uniformiser of the Laurent series field `LaurentSeries F`, taken with its $X$-adic complete ultrametric normed-field structure, and set $q = t^{N}$. Let [`TateCurve.curve q`](def/TateCurve_QSeries.html#L185) be the Weierstrass curve $\langle 1,0,0,a_4(q),a_6(q)\rangle$ over `LaurentSeries F`, i.e. $y^2 + xy = x^3 + a_4(q)x + a_6(q)$ with the project's $q$-series coefficients, and for $u$ in `LaurentSeries F` let $\mathrm{pointX}(q,u) = \bigl(\sum_{n \in \mathbb{Z}} \mathrm{xfun}(q^n u)\bigr) - 2\,s_1(q)$, where `xfun` and `s₁` are the project's series entering the Tate parametrisation. Then for all natural numbers $i, j < N$ with not both $i = 0$ and $j = 0$, the element $\mathrm{pointX}\bigl(q,\ \mathrm{C}(\zeta)^i\, t^{\,j}\bigr)$, formed from the constant Hahn series at $\zeta$ raised to the $i$-th power times $t^{j}$, is a root of the univariate division polynomial `preΨ' N` of [`TateCurve.curve q`](def/TateCurve_QSeries.html#L185).
--
--   This identifies the abscissae of the $N$-torsion points $u = \zeta^i t^j$ of the Tate parametrisation $\mathbb{G}_m/q^{\mathbb{Z}} \simeq E_q$ over $F((t))$, with $q = t^N$, as roots of the $N$-division polynomial, for odd $N$ the classical $\psi_N$. It is used in the construction of explicit points on modular curves, being cited by the evaluations of the division polynomial at the Tate base point and at its toric translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_isRoot_prePsi_curve_pointX_laurentSeries.lean

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped LaurentSeries.XAdic

theorem TateCurve.isRoot_prePsi_curve_pointX_laurentSeries (F : Type) [Field F] [CharZero F]
    (N : ℕ) [NeZero N] (hodd : Odd N) (hN5 : 5 ≤ N) (ζ : F) (hζ : IsPrimitiveRoot ζ N)
    (i j : ℕ) (hi : i < N) (hj : j < N) (hij : ¬ (i = 0 ∧ j = 0)) :
    ((TateCurve.curve ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N)).preΨ' N).IsRoot
      (TateCurve.pointX ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N)
        ((HahnSeries.C : F →+* LaurentSeries F) ζ ^ i
          * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)) := by sorry
