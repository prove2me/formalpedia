-- Prove2me | Theorems.Thm_RubinSilverberg_rsFamilyA_eq_aeval
-- name    : RubinSilverberg.rsFamilyA_eq_aeval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/a5b22fe6-3a49-5cf2-9bc7-e5d7d803644f
-- title:
--   Rubin–Silverberg coefficient a as a polynomial evaluation
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $a,u_0,l\in K$ and let $x\in F$. Write $H(u)=u^{20}-228u^{15}+494u^{10}+228u^{5}+1$ and $H_{\hom}(n,d)=n^{20}-228n^{15}d^{5}+494n^{10}d^{10}+228n^{5}d^{15}+d^{20}$, and let $\beta,\gamma$ be the rational functions `rsBeta`, `rsGamma` built from $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^{5}+1$ by $\beta(u)=T(u)(57u^{15}-247u^{10}-171u^{5}-1)/\bigl(144u^{4}(u^{10}+11u^{5}-1)^{4}\bigr)$ and $\gamma(u)=T(u)(u^{15}-171u^{10}+247u^{5}+57)/\bigl(144(u^{10}+11u^{5}-1)^{4}\bigr)$. The assertion is that
--   $$\frac{a\,H_{\hom}\bigl((\beta(u_0)+l u_0)x+u_0,\ (\gamma(u_0)+l)x+1\bigr)}{H(u_0)},$$
--   formed in $F$ with $a,u_0,l$ replaced by their images under `algebraMap K F` (so that $\beta,\gamma,H,H_{\hom}$ are evaluated in $F$), coincides with the image under `Polynomial.aeval x` of the polynomial $C\bigl(a/H(u_0)\bigr)\cdot H_{\hom}\bigl(C(\beta(u_0)+l u_0)X+C(u_0),\,C(\gamma(u_0)+l)X+1\bigr)\in K[X]$, whose coefficients are formed in $K$. All divisions are Lean field divisions, so both sides are $0$ when $H(u_0)=0$ or a denominator of $\beta,\gamma$ vanishes.
--
--   The statement identifies the pointwise-defined $a$-coefficient of the Rubin–Silverberg family of elliptic curves with constant mod-$p$ representation, parametrised by a Klein datum $u_0$ and a slope $l$, with the evaluation of a single polynomial with coefficients in the base field $K$. It is used in [`RubinSilverberg.exists_torsionBy_linearEquiv_rsMember`](thm.html#RubinSilverberg.exists_torsionBy_linearEquiv_rsMember), where the family must be manipulated as polynomial algebra over an extension field rather than as a function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_rsFamilyA_eq_aeval.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.rsFamilyA_eq_aeval {K F : Type*} [Field K] [Field F] [Algebra K F] (a u₀ l : K) (x : F) : rsFamilyA (algebraMap K F a) (algebraMap K F u₀) (algebraMap K F l) x = Polynomial.aeval x (Polynomial.C (a / kleinH u₀) * kleinHHom (Polynomial.C (rsBeta u₀ + l * u₀) * Polynomial.X + Polynomial.C u₀) (Polynomial.C (rsGamma u₀ + l) * Polynomial.X + 1)) := by sorry
