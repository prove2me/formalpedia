-- Prove2me | Theorems.Thm_RubinSilverberg_isIcoSymmetry_icoU
-- name    : RubinSilverberg.isIcoSymmetry_icoU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/6f4d424b-ce89-59a3-9829-b0231cf129ef
-- title:
--   Klein's icosahedral substitution U is a Rubin–Silverberg symmetry
-- statement:
--   Let $K$ be a field of characteristic zero and let $\zeta \in K$ be a primitive fifth root of unity. Put $s = \zeta + \zeta^4 - \zeta^2 - \zeta^3$ (`sqrtFive`) and let $g =$ `icoU` $\zeta$ be the matrix $s^{-1}\begin{pmatrix} -(\zeta-\zeta^4) & \zeta^2-\zeta^3 \\ \zeta^2-\zeta^3 & \zeta-\zeta^4\end{pmatrix}$. The assertion is that $g$ satisfies `IsIcoSymmetry`, which unfolds into five statements: $\det g = 1$; the three binary forms $V(n,d) = nd(n^{10}+11n^5d^5-d^{10})$, $H(n,d) = n^{20}-228n^{15}d^5+494n^{10}d^{10}+228n^5d^{15}+d^{20}$ and $T(n,d) = n^{30}+522n^{25}d^5-10005n^{20}d^{10}-10005n^{10}d^{20}-522n^5d^{25}+d^{30}$ (`kleinVHom`, `kleinHHom`, `kleinTHom`) are each invariant, for all $n,d \in K$, under the substitution $(n,d) \mapsto (g_{00}n+g_{01}d,\ g_{10}n+g_{11}d)$; and, for every $u \in K$ with $u(u^{10}+11u^5-1) \neq 0$ and $g_{10}u+g_{11} \neq 0$, writing $gu = (g_{00}u+g_{01})/(g_{10}u+g_{11})$, the pair of rational functions $\beta,\gamma$ of the Rubin–Silverberg family (`rsBeta`, `rsGamma`, built from the form `kleinT` as displayed) transforms as a vector of weight $-1$: $(g_{10}u+g_{11})\beta(gu) = g_{00}\beta(u)+g_{01}\gamma(u)$ and $(g_{10}u+g_{11})\gamma(gu) = g_{10}\beta(u)+g_{11}\gamma(u)$.
--
--   This is the invariance of Klein's vertex, face and edge forms and of the Rubin–Silverberg Möbius datum under the third of Klein's generators of the binary icosahedral group in $\mathrm{SL}_2(K)$, the one not fixing the coordinate points (the substitutions $u \mapsto \zeta u$ and $u \mapsto -1/u$ being the other two). It is used in the proof that the third division polynomial of the Klein curve of the family does not vanish at the relevant parameters ([`RubinSilverberg.kleinCurve_Psi3_eval_ne_zero`](thm.html#RubinSilverberg.kleinCurve_Psi3_eval_ne_zero)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_isIcoSymmetry_icoU.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.isIcoSymmetry_icoU {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : IsIcoSymmetry (icoU ζ) := by sorry
