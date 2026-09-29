-- Prove2me | Theorems.Thm_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember
-- name    : RubinSilverberg.exists_variableChange_kleinCurve_eq_rsMember
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/911da6d2-2fe8-5967-9278-281ce3ab65a1
-- title:
--   Rescaling Klein's curve onto the Rubin–Silverberg member
-- statement:
--   Let $K$ be a field of characteristic zero and let $a,b,u_0\in K$. Write $V(u)=u(u^{10}+11u^5-1)$, $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$ and $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$. Assume `IsKleinDatum a b u₀`, i.e. $H(u_0)^3(4a^3+27b^2)+6912\,a^3V(u_0)^5=0$ and $V(u_0)\neq 0$, and assume $a\neq 0$ and $b\neq 0$. Let $l,t,k\in K$ be such that the denominator $\mathrm{den}=(\mathrm{rsGamma}(u_0)+l)t+1$ is non-zero and $k^2=-18(b/a)H(u_0)/T(u_0)$, where $\mathrm{rsGamma}(u)=T(u)(u^{15}-171u^{10}+247u^5+57)/\bigl(144(u^{10}+11u^5-1)^4\bigr)$. Then there is a Weierstrass variable change $C=(u;r,s,t)$ over $K$ with $C.u^{-1}=k\cdot\mathrm{den}^5$ and $r=s=t=0$ such that $C$ carries the Klein curve $y^2=x^3-\tfrac{H(\nu)}{48}x+\tfrac{T(\nu)}{864}$ at the parameter $\nu=\mathrm{num}/\mathrm{den}$, with $\mathrm{num}=(\mathrm{rsBeta}(u_0)+lu_0)t+u_0$, to the family member $y^2=x^3+a\,\tfrac{\mathrm{kleinHHom}(\mathrm{num},\mathrm{den})}{H(u_0)}x+b\,\tfrac{\mathrm{kleinTHom}(\mathrm{num},\mathrm{den})}{T(u_0)}$, where $\mathrm{kleinHHom}$ and $\mathrm{kleinTHom}$ are the two-variable forms with $H(n/d)=\mathrm{kleinHHom}(n,d)/d^{20}$ and $T(n/d)=\mathrm{kleinTHom}(n,d)/d^{30}$.
--
--   This is the rescaling step of the Rubin–Silverberg construction of families of elliptic curves with constant mod $5$ representation: each member of the family is, after an explicit scaling by $k\cdot\mathrm{den}^5$ involving the square root $k$, a model of Klein's level-$5$ curve at the parameter $\mathrm{num}/\mathrm{den}$. It is the bridge along which $5$-torsion data are transported, and it is used by the statements on the $5$-torsion subgroup of a member, on the non-vanishing and $5$-divisibility of the distinguished point, and on independence of the sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.exists_variableChange_kleinCurve_eq_rsMember {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) (hb : b ≠ 0) (l t k : K) (hden : rsDen u₀ l t ≠ 0) (hk : k ^ 2 = -18 * (b / a) * kleinH u₀ / kleinT u₀) : ∃ C : WeierstrassCurve.VariableChange K, (↑C.u⁻¹ : K) = k * rsDen u₀ l t ^ 5 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ C • kleinCurve (rsNum u₀ l t / rsDen u₀ l t) = rsMember a b u₀ l t := by sorry
