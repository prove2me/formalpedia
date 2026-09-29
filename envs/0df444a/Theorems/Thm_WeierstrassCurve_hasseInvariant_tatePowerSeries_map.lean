-- Prove2me | Theorems.Thm_WeierstrassCurve_hasseInvariant_tatePowerSeries_map
-- name    : WeierstrassCurve.hasseInvariant_tatePowerSeries_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/d3b46d2a-5e02-5bdd-8677-e71a02fd1816
-- title:
--   Hasse invariant of the Tate curve is 1
-- statement:
--   Let $q$ be a prime with $q \neq 2$. Over the ring $\mathbb{Z}[[\mathfrak q]]$ of formal power series, [`ModularCurve.tatePowerSeries`](def/ModularCurve_TateFormal.html#L72) denotes the Weierstrass curve with coefficients $a_1 = 1$, $a_2 = a_3 = 0$, $a_4 =$ `tateA4` $= \sum_{n} \bigl(-\sum_{d \mid n} 5 d^{3}\bigr)\mathfrak q^{n}$ and $a_6 =$ `tateA6` $= \sum_{n}\bigl(-\sum_{d \mid n} \mathrm{tateB}\,d\bigr)\mathfrak q^{n}$, the sums being over the positive divisors $d$ of $n$ and $\mathrm{tateB}$ being the integer-valued function appearing in the definition. This curve is pushed forward along the ring homomorphism $\mathbb{Z}[[\mathfrak q]] \to (\mathbb{Z}/q)[[\mathfrak q]]$ induced coefficientwise by reduction modulo $q$. For a Weierstrass curve $W$ over a commutative ring, [`WeierstrassCurve.hasseInvariant q W`](def/WeierstrassCurve_HasseInvariant.html#L11) is by definition the coefficient of $X^{q-1}$ in the $((q-1)/2)$-th power of the polynomial attached to the two-torsion cubic $4X^{3} + b_2 X^{2} + 2 b_4 X + b_6$ of $W$ (with natural-number subtraction and division). The assertion is that for the reduced Tate curve this coefficient equals $1$ in $(\mathbb{Z}/q)[[\mathfrak q]]$.
--
--   This is the classical statement that the Hasse invariant of the Tate curve is $1$, equivalently that the $\mathfrak q$-expansion of $E_{q-1}$ modulo $q$ is $1$. It is the input used in the identification of $\Delta^{1-q} \bmod q$ with the weighted supersingular polynomial, and is cited by [`ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve`](thm.html#ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve) and [`ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one`](thm.html#ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_hasseInvariant_tatePowerSeries_map.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_tatePowerSeries_map
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    WeierstrassCurve.hasseInvariant q (ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))) = 1 := by sorry
