-- Prove2me | Theorems.Thm_RubinSilverberg_rsFamilyB_eq_aeval
-- name    : RubinSilverberg.rsFamilyB_eq_aeval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/f49c19df-9858-5ecb-b207-1e486151c637
-- title:
--   The Rubin–Silverberg coefficient b(t) as a polynomial evaluation
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $b,u_0,l\in K$ and let $x\in F$. Write $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^{5}+1$ for `kleinT`, $T_{\hom}(n,d)=n^{30}+522n^{25}d^{5}-10005n^{20}d^{10}-10005n^{10}d^{20}-522n^{5}d^{25}+d^{30}$ for its homogenisation `kleinTHom`, and let $\beta(u)=T(u)(57u^{15}-247u^{10}-171u^{5}-1)/\bigl(144u^{4}(u^{10}+11u^{5}-1)^{4}\bigr)$ and $\gamma(u)=T(u)(u^{15}-171u^{10}+247u^{5}+57)/\bigl(144(u^{10}+11u^{5}-1)^{4}\bigr)$ be `rsBeta` and `rsGamma`. The assertion is that
--   $$\frac{\iota(b)\,T_{\hom}\bigl((\beta(\iota u_0)+\iota(l)\iota(u_0))x+\iota(u_0),\;(\gamma(\iota u_0)+\iota l)x+1\bigr)}{T(\iota u_0)},$$ i.e. the value `rsFamilyB` at the images $\iota(b),\iota(u_0),\iota(l)$ under the structure map $\iota=$ `algebraMap K F` and at the point $x$, coincides with the evaluation at $x$ of the polynomial
--   $$C\!\left(b/T(u_0)\right)\cdot T_{\hom}\bigl(C(\beta(u_0)+l u_0)X+C(u_0),\;C(\gamma(u_0)+l)X+1\bigr)\in K[X]$$
--   under `Polynomial.aeval`. No nonvanishing hypotheses are imposed: where $T(u_0)=0$, or in characteristics where the denominators of $\beta,\gamma$ vanish, both sides take the value dictated by Lean's convention for division and the identity is vacuous.
--
--   The Rubin–Silverberg construction parametrises, over a one-dimensional family with Klein datum $u_0$ and slope parameter $l$, curves whose coefficients are given by the homogenised Klein form $T_{\hom}$; this statement records that the $b$-coefficient of the family, as a function of the parameter $t$, is the evaluation of a single polynomial with coefficients in the base field $K$, so that base change along $K\to F$ and specialisation commute. It is used in [`RubinSilverberg.exists_torsionBy_linearEquiv_rsMember`](thm.html#RubinSilverberg.exists_torsionBy_linearEquiv_rsMember), and is the companion of the corresponding statement for the $a$-coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_rsFamilyB_eq_aeval.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.rsFamilyB_eq_aeval {K F : Type*} [Field K] [Field F] [Algebra K F] (b u₀ l : K) (x : F) : rsFamilyB (algebraMap K F b) (algebraMap K F u₀) (algebraMap K F l) x = Polynomial.aeval x (Polynomial.C (b / kleinT u₀) * kleinTHom (Polynomial.C (rsBeta u₀ + l * u₀) * Polynomial.X + Polynomial.C u₀) (Polynomial.C (rsGamma u₀ + l) * Polynomial.X + 1)) := by sorry
