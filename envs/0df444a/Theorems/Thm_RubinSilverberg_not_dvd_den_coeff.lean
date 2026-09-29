-- Prove2me | Theorems.Thm_RubinSilverberg_not_dvd_den_coeff
-- name    : RubinSilverberg.not_dvd_den_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/574ee601-ac26-5800-aa67-8092f3789dde
-- title:
--   p-integrality of the Rubin–Silverberg family coefficients
-- statement:
--   Let $a,b,l$ be integers and let $u_0$ lie in an algebraic closure of $\mathbb{Q}$, and suppose $(a,b,u_0)$ (with $a,b$ viewed in $\overline{\mathbb{Q}}$) is a Klein datum, i.e. $H(u_0)^3\,(4a^3+27b^2)+6912\,a^3\,V(u_0)^5=0$ and $V(u_0)\neq 0$, where $V(u)=u(u^{10}+11u^5-1)$ and $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$. Let $p$ be a prime with $p\nmid 30$, $p\nmid a$, $p\nmid b$ and $p\nmid 4a^3+27b^2$. Let $p_a,p_b\in\mathbb{Q}[t]$ be polynomials which, after base change to $\overline{\mathbb{Q}}$, compute the two Rubin–Silverberg coordinate functions at every $t\in\overline{\mathbb{Q}}$: writing $n=(\beta(u_0)+l\,u_0)t+u_0$ and $d=(\gamma(u_0)+l)t+1$ for the quantities `rsBeta u₀`, `rsGamma u₀`, one requires $p_a(t)=a\,H^{\mathrm{hom}}(n,d)/H(u_0)$ and $p_b(t)=b\,T^{\mathrm{hom}}(n,d)/T(u_0)$, where $H^{\mathrm{hom}}(n,d)=n^{20}-228n^{15}d^5+494n^{10}d^{10}+228n^5d^{15}+d^{20}$, $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$ and $T^{\mathrm{hom}}(n,d)=n^{30}+522n^{25}d^5-10005n^{20}d^{10}-10005n^{10}d^{20}-522n^5d^{25}+d^{30}$. The conclusion is that for every index $k$ the denominator of the rational coefficient $p_a$ at $k$ is not divisible by $p$, and likewise for $p_b$.
--
--   This is the $p$-integrality input for the Rubin–Silverberg $3$–$5$ switching construction: the two rational functions cutting out the family of curves with prescribed mod-$5$ representation have coefficients integral at every prime outside the excluded set $\{2,3,5\}\cup\{p : p\mid ab(4a^3+27b^2)\}$. It is used in the construction of the auxiliary curve, [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists), where good reduction of a member of the family away from that set must be controlled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_not_dvd_den_coeff.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.not_dvd_den_coeff {a b l : ℤ} {u₀ : AlgebraicClosure ℚ} (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀) {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : Polynomial ℚ} (hpa' : ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) (hpb' : ∀ t : AlgebraicClosure ℚ, rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) : (∀ k, ¬ p ∣ (pa.coeff k).den) ∧ ∀ k, ¬ p ∣ (pb.coeff k).den := by sorry
