-- Prove2me | Theorems.Thm_RubinSilverberg_rsMember_zero
-- name    : RubinSilverberg.rsMember_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/c29cf3da-1190-5b89-8fd8-3a0951512d49
-- title:
--   Rubin–Silverberg family at t=0 is the base curve
-- statement:
--   Let $K$ be a field and let $a,b,u_0,\lambda \in K$. Assume that the two Klein invariants at $u_0$ are nonzero, namely $\mathrm{kleinH}(u_0) = u_0^{20} - 228u_0^{15} + 494u_0^{10} + 228u_0^{5} + 1 \neq 0$ and $\mathrm{kleinT}(u_0) = u_0^{30} + 522u_0^{25} - 10005u_0^{20} - 10005u_0^{10} - 522u_0^{5} + 1 \neq 0$. The assertion is that the member of the Rubin–Silverberg family at parameter value $t = 0$, that is the Weierstrass curve `rsMember a b u₀ l 0` whose coefficients are $a_1 = a_2 = a_3 = 0$ together with
--   $$a_4 = a\,\frac{\mathrm{kleinHHom}(\mathrm{rsNum}\,u_0\,\lambda\,0,\ \mathrm{rsDen}\,u_0\,\lambda\,0)}{\mathrm{kleinH}(u_0)}, \qquad a_6 = b\,\frac{\mathrm{kleinTHom}(\mathrm{rsNum}\,u_0\,\lambda\,0,\ \mathrm{rsDen}\,u_0\,\lambda\,0)}{\mathrm{kleinT}(u_0)},$$
--   where `kleinHHom` and `kleinTHom` are the two-variable forms attached to `kleinH` and `kleinT` and `rsNum`, `rsDen` are the numerator and denominator of the parametrising fraction, coincides with the Weierstrass curve $\langle 0,0,0,a,b\rangle$, i.e. $y^2 = x^3 + ax + b$. Thus the family is normalised so that its value at $t = 0$ is the given base curve, for every choice of slope parameter $\lambda$.
--
--   This is the normalisation statement "$E_0 = E$" for the Rubin–Silverberg family of elliptic curves with prescribed mod $5$ representation: the family through $y^2 = x^3 + ax + b$ attached to the data $u_0,\lambda$ passes through the base curve at the parameter value $0$. It is used in the construction of the auxiliary curve with prescribed $5$-torsion, being cited by [`RubinSilverberg.exists_torsionBy_linearEquiv_rsMember`](thm.html#RubinSilverberg.exists_torsionBy_linearEquiv_rsMember) and [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_rsMember_zero.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.rsMember_zero {K : Type*} [Field K] (a b u₀ l : K) (hH : kleinH u₀ ≠ 0) (hT : kleinT u₀ ≠ 0) : rsMember a b u₀ l 0 = ⟨0, 0, 0, a, b⟩ := by sorry
