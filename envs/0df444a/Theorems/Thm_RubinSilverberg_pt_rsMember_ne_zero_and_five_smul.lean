-- Prove2me | Theorems.Thm_RubinSilverberg_pt_rsMember_ne_zero_and_five_smul
-- name    : RubinSilverberg.pt_rsMember_ne_zero_and_five_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/a4c92e7c-a56e-5361-bec5-ccdfc4175863
-- title:
--   A nonzero 5-torsion point on the Rubin–Silverberg member
-- statement:
--   Let $K$ be a field of characteristic zero and let $a,b,u_0\in K$ satisfy the Klein datum condition `IsKleinDatum a b u₀`, that is $H(u_0)^3(4a^3+27b^2)+6912\,a^3V(u_0)^5=0$ and $V(u_0)\neq 0$, where $V(u)=u(u^{10}+11u^5-1)$ and $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$; assume moreover $a\neq 0$ and $b\neq 0$. Let $l,t,k,w\in K$ and write $\mathrm{rsNum}=(\beta(u_0)+lu_0)t+u_0$ and $\mathrm{rsDen}=(\gamma(u_0)+l)t+1$ for the numerator and denominator of the family parameter, with $\beta=$ `rsBeta`, $\gamma=$ `rsGamma`, and put $v=\mathrm{rsNum}/\mathrm{rsDen}$. Assume $\mathrm{rsDen}\neq 0$, $V(v)\neq 0$, $k^2=-18(b/a)H(u_0)/T(u_0)$ with $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$, and $w^5=v^5$. Let $E_t=$ `rsMember a b u₀ l t` be the Weierstrass curve $\langle 0,0,0,\;a\,\mathrm{kleinHHom}(\mathrm{rsNum},\mathrm{rsDen})/H(u_0),\;b\,\mathrm{kleinTHom}(\mathrm{rsNum},\mathrm{rsDen})/T(u_0)\rangle$, with coefficients given by `kleinHHom` and `kleinTHom`. Then the point of the affine point group of $E_t$ obtained by `pt` from the coordinates $\bigl(k^2\,\mathrm{rsDen}^{10}\,X(w),\;k^3\,\mathrm{rsDen}^{15}\,Y(w)\bigr)$, where $X$ and $Y$ are the explicit degree-$10$ and degree-$13$ rational expressions `kleinX` and `kleinY`, is nonzero and is killed by $5$. (Since `pt` returns $0$ at a singular pair, nonvanishing in particular asserts that this pair is a nonsingular point of $E_t$.)
--
--   This transports Klein's explicit $5$-torsion sections on the icosahedral curve `kleinCurve v` to the members of the Rubin–Silverberg family, exhibiting on each member an explicit $K$-rational point of exact order $5$. It is the input to [`RubinSilverberg.exists_torsionBy_linearEquiv_rsMember`](thm.html#RubinSilverberg.exists_torsionBy_linearEquiv_rsMember), on the way to the constancy of the mod-$5$ representation along the family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_pt_rsMember_ne_zero_and_five_smul.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.pt_rsMember_ne_zero_and_five_smul {K : Type*} [Field K] [CharZero K] [DecidableEq K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) (hb : b ≠ 0) (l t k w : K) (hden : rsDen u₀ l t ≠ 0) (hV : kleinV (rsNum u₀ l t / rsDen u₀ l t) ≠ 0) (hk : k ^ 2 = -18 * (b / a) * kleinH u₀ / kleinT u₀) (hw : w ^ 5 = (rsNum u₀ l t / rsDen u₀ l t) ^ 5) : pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX w) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY w) ≠ 0 ∧ (5 : ℤ) • pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX w) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY w) = 0 := by sorry
