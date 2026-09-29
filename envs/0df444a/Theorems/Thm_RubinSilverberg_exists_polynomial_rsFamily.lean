-- Prove2me | Theorems.Thm_RubinSilverberg_exists_polynomial_rsFamily
-- name    : RubinSilverberg.exists_polynomial_rsFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/b5a6aa77-a4ed-5ae1-a7fe-d0d89b17ae8d
-- title:
--   Rationality of the Rubin–Silverberg family coefficients
-- statement:
--   Let $a,b,l\in\mathbb{Q}$ with $a\neq 0$ and $b\neq 0$, and let $u_0\in\overline{\mathbb{Q}}$ be an element such that the pair $(a,b)$, viewed in $\overline{\mathbb{Q}}$, together with $u_0$ satisfies `IsKleinDatum`, i.e. $H(u_0)^3(4a^3+27b^2)+6912\,a^3V(u_0)^5=0$ and $V(u_0)\neq 0$, where $V(u)=u(u^{10}+11u^5-1)$ and $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$. Put $N(t)=(\mathrm{rsBeta}(u_0)+lu_0)t+u_0$ and $D(t)=(\mathrm{rsGamma}(u_0)+l)t+1$, and let $\tilde H(n,d)=n^{20}-228n^{15}d^5+494n^{10}d^{10}+228n^5d^{15}+d^{20}$, $\tilde T(n,d)=n^{30}+522n^{25}d^5-10005n^{20}d^{10}-10005n^{10}d^{20}-522n^5d^{25}+d^{30}$ be the two homogenised Klein forms, with $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$. The assertion is that there exist polynomials $p_a,p_b\in\mathbb{Q}[t]$ with $\deg p_a\le 20$ and $\deg p_b\le 30$ such that for every $t\in\overline{\mathbb{Q}}$ one has $a\,\tilde H(N(t),D(t))/H(u_0)=p_a(t)$ and $b\,\tilde T(N(t),D(t))/T(u_0)=p_b(t)$, the polynomials being evaluated after mapping their coefficients from $\mathbb{Q}$ into $\overline{\mathbb{Q}}$.
--
--   This is the rationality statement for the coefficient functions of the Rubin–Silverberg family of curves with prescribed mod $5$ torsion: although the family is built from a Klein parameter $u_0$ lying in $\overline{\mathbb{Q}}$, the resulting $a(t)$ and $b(t)$ are values of polynomials defined over $\mathbb{Q}$, of degrees at most $20$ and $30$. It is used in the construction of members of the family with prescribed $5$-torsion and in the production of the auxiliary curve for the $3$–$5$ switch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_exists_polynomial_rsFamily.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.exists_polynomial_rsFamily (a b l : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (u₀ : AlgebraicClosure ℚ) (h : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀) : ∃ pa pb : Polynomial ℚ, pa.natDegree ≤ 20 ∧ pb.natDegree ≤ 30 ∧ ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) a) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t ∧ rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t := by sorry
