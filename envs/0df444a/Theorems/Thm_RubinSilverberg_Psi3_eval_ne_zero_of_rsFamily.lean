-- Prove2me | Theorems.Thm_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily
-- name    : RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/e4d7bab6-649a-5ea2-b89d-417112acd546
-- title:
--   Ψ₃ of the Rubin–Silverberg family has no polynomial root
-- statement:
--   Let $K$ and $F$ be fields with $F$ of characteristic zero and algebraically closed, and let $F$ be a $K$-algebra; write $\iota$ for the structure map $K \to F$. Let $a, b, l \in K$ with $a \neq 0$ and $b \neq 0$, and let $u_0 \in F$ satisfy the project's predicate `IsKleinDatum` for $(\iota a, \iota b, u_0)$, which unfolds to the two conditions $\mathrm{kleinH}(u_0)^3\,(4(\iota a)^3 + 27(\iota b)^2) + 6912\,(\iota a)^3\,\mathrm{kleinV}(u_0)^5 = 0$ and $\mathrm{kleinV}(u_0) \neq 0$, where $\mathrm{kleinV}, \mathrm{kleinH}, \mathrm{kleinT}$ are the explicit Klein forms of degrees $11$, $20$, $30$ defined in the project. Let $p_a, p_b \in K[X]$ be polynomials whose coefficientwise images in $F[X]$ agree, as functions on all of $F$, with the two coefficient functions of the Rubin–Silverberg family through $u_0$ with parameter $\iota l$: for every $t \in F$ one has $(p_a^{\iota})(t) = \mathrm{rsFamilyA}(\iota a, u_0, \iota l, t)$ and $(p_b^{\iota})(t) = \mathrm{rsFamilyB}(\iota b, u_0, \iota l, t)$, where $\mathrm{rsFamilyA}(a,u_0,l,t) = a\,\mathrm{kleinHHom}(\mathrm{rsNum},\mathrm{rsDen})/\mathrm{kleinH}(u_0)$ and $\mathrm{rsFamilyB}(b,u_0,l,t) = b\,\mathrm{kleinTHom}(\mathrm{rsNum},\mathrm{rsDen})/\mathrm{kleinT}(u_0)$ with $\mathrm{rsNum} = (\mathrm{rsBeta}(u_0) + l u_0)t + u_0$ and $\mathrm{rsDen} = (\mathrm{rsGamma}(u_0) + l)t + 1$. The conclusion is that for the Weierstrass curve over the ring $K[X]$ given by $(a_1,a_2,a_3,a_4,a_6) = (0,0,0,p_a,p_b)$, Mathlib's third division polynomial $\Psi_3$ (a polynomial in one variable over $K[X]$) has no root in $K[X]$: for every $g \in K[X]$, $\Psi_3(g) \neq 0$. Note that the assertion is only about polynomial arguments $g$, not about arbitrary elements of $K(X)$.
--
--   This is the rootlessness input for the Rubin–Silverberg $3$–$5$ switch: the family of curves $y^2 = x^3 + a(t)x + b(t)$ attached to a Klein datum $u_0$ is designed to have constant mod-$5$ representation, and one needs that no member acquires a rational $3$-division point generically, i.e. that the $3$-division polynomial of the family has no root in the coefficient ring. Compared with a textbook formulation, the hypotheses do not presuppose that $p_a, p_b$ are given by the family's formulae as polynomial identities: they are only assumed to agree with the family pointwise on $F$, and the Klein datum lives over the algebraically closed field $F$ rather than over $K$. The result is used in [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists), which produces, from a semistable $W/\mathbb{Q}$ with irreducible mod-$5$ representation, a second semistable curve with irreducible mod-$3$ representation and Galois-equivariantly isomorphic $5$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily {K F : Type*} [Field K] [Field F] [CharZero F] [IsAlgClosed F] [Algebra K F] {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀) {pa pb : Polynomial K} (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t) (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t) (g : Polynomial K) : ((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve (Polynomial K)).Ψ₃).eval g ≠ 0 := by sorry
