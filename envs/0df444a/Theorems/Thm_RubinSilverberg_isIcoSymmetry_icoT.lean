-- Prove2me | Theorems.Thm_RubinSilverberg_isIcoSymmetry_icoT
-- name    : RubinSilverberg.isIcoSymmetry_icoT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/af128388-6f9a-5385-91fc-cf4038b98d69
-- title:
--   The involution u↦-1/u is an icosahedral symmetry
-- statement:
--   Let $K$ be a field of characteristic zero. The assertion is that the matrix $\mathrm{icoT}=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\in\mathrm{Matrix}\,(\mathrm{Fin}\,2)\,(\mathrm{Fin}\,2)\,K$ satisfies the predicate `IsIcoSymmetry`, i.e. all of the following. First, its determinant is $1$. Second, the three binary forms $V(n,d)=nd(n^{10}+11n^5d^5-d^{10})$, $H(n,d)=n^{20}-228n^{15}d^5+494n^{10}d^{10}+228n^5d^{15}+d^{20}$ and $T(n,d)=n^{30}+522n^{25}d^5-10005n^{20}d^{10}-10005n^{10}d^{20}-522n^5d^{25}+d^{30}$ are each invariant under the substitution $(n,d)\mapsto(d,-n)$, for all $n,d\in K$. Third, for every $u\in K$ with $u(u^{10}+11u^5-1)\neq0$ and with $\mathrm{moebDen}$ at $u$, namely $-u$, nonzero, the pair $(\beta,\gamma)=(\mathrm{rsBeta},\mathrm{rsGamma})$, where
--   $$\beta(u)=\frac{\mathrm{kleinT}(u)\,(57u^{15}-247u^{10}-171u^5-1)}{144u^4(u^{10}+11u^5-1)^4},\qquad \gamma(u)=\frac{\mathrm{kleinT}(u)\,(u^{15}-171u^{10}+247u^5+57)}{144(u^{10}+11u^5-1)^4},$$
--   transforms as $-u\,\beta(-u^{-1})=\gamma(u)$ and $-u\,\gamma(-u^{-1})=-\beta(u)$, the Möbius action of $\mathrm{icoT}$ on $u$ being $-u^{-1}$. In particular the involution interchanges $\beta$ and $\gamma$ up to sign.
--
--   The matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ is one of the generators of the binary icosahedral group acting on the parameter $u$ of the Rubin–Silverberg family of elliptic curves with prescribed mod $5$ representation; the statement records that it preserves Klein's icosahedral forms $V$, $H$, $T$ and acts on the pair $(\beta,\gamma)$ by the same linear substitution. It is used in the proof of [`RubinSilverberg.kleinCurve_Psi3_eval_ne_zero`](thm.html#RubinSilverberg.kleinCurve_Psi3_eval_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_isIcoSymmetry_icoT.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.isIcoSymmetry_icoT {K : Type*} [Field K] [CharZero K] : IsIcoSymmetry (icoT : Matrix (Fin 2) (Fin 2) K) := by sorry
