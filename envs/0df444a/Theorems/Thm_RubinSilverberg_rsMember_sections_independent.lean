-- Prove2me | Theorems.Thm_RubinSilverberg_rsMember_sections_independent
-- name    : RubinSilverberg.rsMember_sections_independent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/aca776b6-9fa0-590d-80c5-45d94df61c89
-- title:
--   Independence mod 5 of the two Klein sections on E_{l,t}
-- statement:
--   Let $K$ be a field of characteristic $0$ and let $\zeta \in K$ be a primitive fifth root of unity. Let $a,b,u_0 \in K$ satisfy `IsKleinDatum a b u₀`, i.e. $H(u_0)^3(4a^3+27b^2)+6912\,a^3 V(u_0)^5=0$ and $V(u_0)\neq 0$, where $V(u)=u(u^{10}+11u^5-1)$, $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$, and also let $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$; assume $a\neq 0$ and $b\neq 0$. Let $l,t,k\in K$ with $\mathrm{rsDen}(u_0,l,t)=(\mathrm{rsGamma}(u_0)+l)t+1\neq 0$, put $v=\mathrm{rsNum}(u_0,l,t)/\mathrm{rsDen}(u_0,l,t)$ with $\mathrm{rsNum}(u_0,l,t)=(\mathrm{rsBeta}(u_0)+l u_0)t+u_0$, assume $V(v)\neq 0$, and assume $k^2=-18(b/a)H(u_0)/T(u_0)$. Let $E=$ `rsMember a b u₀ l t` be the Weierstrass curve $y^2=x^3+Ax+B$ with $A=a\cdot \mathrm{kleinHHom}(\mathrm{rsNum},\mathrm{rsDen})/H(u_0)$ and $B=b\cdot \mathrm{kleinTHom}(\mathrm{rsNum},\mathrm{rsDen})/T(u_0)$. For $w\in K$ write $P(w)$ for the affine point of $E$ with coordinates $\big(k^2\mathrm{rsDen}^{10}X(w),\,k^3\mathrm{rsDen}^{15}Y(w)\big)$, where $X$ and $Y$ are the explicit Klein rational functions `kleinX`, `kleinY` and `pt` returns that point when the pair is nonsingular on $E$ and $0$ otherwise. Then for integers $i,j$ with $i\cdot P(v)+j\cdot P(\zeta v)=0$ in $E(K)$, one has $5\mid i$ and $5\mid j$.
--
--   This is the independence statement for the pair of explicit $K$-rational $5$-torsion sections on a member of the Rubin–Silverberg family, transported from Klein's curve $B_v$ by the scaling with $u^{-1}=k\,\mathrm{rsDen}^5$. Together with the nonvanishing and $5$-torsion properties of the two points it is used by [`RubinSilverberg.exists_torsionBy_linearEquiv_rsMember`](thm.html#RubinSilverberg.exists_torsionBy_linearEquiv_rsMember) to exhibit a $\mathbb{Z}/5$-basis of $E[5]$ defined over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_rsMember_sections_independent.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.rsMember_sections_independent {K : Type*} [Field K] [CharZero K] [DecidableEq K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) (hb : b ≠ 0) (l t k : K) (hden : rsDen u₀ l t ≠ 0) (hV : kleinV (rsNum u₀ l t / rsDen u₀ l t) ≠ 0) (hk : k ^ 2 = -18 * (b / a) * kleinH u₀ / kleinT u₀) (i j : ℤ) (h : i • pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX (rsNum u₀ l t / rsDen u₀ l t)) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY (rsNum u₀ l t / rsDen u₀ l t)) + j • pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX (ζ * (rsNum u₀ l t / rsDen u₀ l t))) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY (ζ * (rsNum u₀ l t / rsDen u₀ l t))) = 0) : (5 : ℤ) ∣ i ∧ (5 : ℤ) ∣ j := by sorry
