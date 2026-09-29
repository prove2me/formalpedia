-- Prove2me | Theorems.Thm_RubinSilverberg_not_dvd_num_eval_and
-- name    : RubinSilverberg.not_dvd_num_eval_and
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/0f24cd4b-2c92-5c15-80a5-1ac80e0a9f63
-- title:
--   Coprimality of the specialised Rubin–Silverberg coefficients at p∤ 30
-- statement:
--   Let $a,b,\lambda$ be integers and let $u_0$ lie in an algebraic closure of $\mathbb Q$, and suppose the triple $(a,b,u_0)$ (with $a,b$ viewed in $\overline{\mathbb Q}$) satisfies `IsKleinDatum`, that is $H(u_0)^3(4a^3+27b^2)+6912\,a^3V(u_0)^5=0$ and $V(u_0)\neq 0$, where $V(u)=u(u^{10}+11u^5-1)$ and $H(u)=u^{20}-228u^{15}+494u^{10}+228u^5+1$. Let $p$ be a prime with $p\nmid 30$, $p\nmid a$, $p\nmid b$ and $p\nmid 4a^3+27b^2$. Let $p_a,p_b\in\mathbb Q[t]$ be polynomials representing the two coefficient functions of the Rubin–Silverberg family over $\overline{\mathbb Q}$: for all $t\in\overline{\mathbb Q}$ one has $a\,H^{\mathrm{hom}}(N(t),D(t))/H(u_0)=p_a(t)$ and $b\,T^{\mathrm{hom}}(N(t),D(t))/T(u_0)=p_b(t)$, where $N(t)=(\beta(u_0)+\lambda u_0)t+u_0$ and $D(t)=(\gamma(u_0)+\lambda)t+1$ with $\beta,\gamma$ given by `rsBeta`, `rsGamma`, $H^{\mathrm{hom}},T^{\mathrm{hom}}$ the homogenisations of $H$ and of $T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^5+1$, and the polynomials are evaluated after base change to $\overline{\mathbb Q}$. Then for every integer $t_0$, $p$ does not divide both numerators $\mathrm{num}\,p_a(t_0)$ and $\mathrm{num}\,p_b(t_0)$.
--
--   This is the local coprimality input for the Rubin–Silverberg construction of elliptic curves with prescribed mod $5$ representation: away from $2,3,5$ and the primes dividing $ab(4a^3+27b^2)$, the specialised pair $(p_a(t_0),p_b(t_0))$ cannot be simultaneously $p$-divisible in the numerators, which is what prevents the specialised curve from acquiring additive reduction at $p$. It is used in the existence proof for the auxiliary curve of the $3$–$5$ switch, [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_not_dvd_num_eval_and.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.not_dvd_num_eval_and {a b l : ℤ} {u₀ : AlgebraicClosure ℚ} (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀) {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : Polynomial ℚ} (hpa' : ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) (hpb' : ∀ t : AlgebraicClosure ℚ, rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) (t₀ : ℤ) : ¬ ((p : ℤ) ∣ (pa.eval (t₀ : ℚ)).num ∧ (p : ℤ) ∣ (pb.eval (t₀ : ℚ)).num) := by sorry
