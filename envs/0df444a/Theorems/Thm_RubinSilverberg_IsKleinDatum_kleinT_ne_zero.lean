-- Prove2me | Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinT_ne_zero
-- name    : RubinSilverberg.IsKleinDatum.kleinT_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/19536979-3c62-54e6-9683-7dbc6ebb18db
-- title:
--   Non-vanishing of Klein's form T at a Klein datum
-- statement:
--   Let $K$ be a field of characteristic zero and let $a,b,u_0\in K$. Write $V(u)=u(u^{10}+11u^5-1)$, $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$ and $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$ for the three Klein forms `kleinV`, `kleinH`, `kleinT`. Assume that $u_0$ is a Klein datum for $(a,b)$ in the sense of the predicate [`RubinSilverberg.IsKleinDatum`](def/EllipticCurve_RubinSilverbergFamily.html#L86), that is, the two conditions
--   $$H(u_0)^3\,(4a^3+27b^2)+6912\,a^3\,V(u_0)^5=0,\qquad V(u_0)\neq 0$$
--   hold. Assume further that $b\neq 0$. Then $T(u_0)\neq 0$.
--
--   This is one of the non-degeneracy facts about Klein's icosahedral forms needed to make the Rubin–Silverberg family of elliptic curves with prescribed mod-$5$ representation well defined, $T(u_0)$ occurring in a denominator there. It is used downstream in the construction of members of that family and in the verification that their discriminants and division-polynomial values are non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_IsKleinDatum_kleinT_ne_zero.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.IsKleinDatum.kleinT_ne_zero {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : RubinSilverberg.IsKleinDatum a b u₀) (hb : b ≠ 0) : RubinSilverberg.kleinT u₀ ≠ 0 := by sorry
