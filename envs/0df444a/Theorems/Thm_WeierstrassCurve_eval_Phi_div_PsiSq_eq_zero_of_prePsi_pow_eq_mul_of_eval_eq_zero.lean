-- Prove2me | Theorems.Thm_WeierstrassCurve_eval_Phi_div_PsiSq_eq_zero_of_prePsi_pow_eq_mul_of_eval_eq_zero
-- name    : WeierstrassCurve.eval_Phi_div_PsiSq_eq_zero_of_prePsi_pow_eq_mul_of_eval_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/12ab2a70-4326-56d1-ac06-ac129926feaf
-- title:
--   Abscissae of exact order p^k are stable under [a], p ∤ a
-- statement:
--   Let $A$ be a commutative ring, $W$ a Weierstrass curve over $A$, $p$ a prime and $k$ a natural number, and assume that $p \cdot \Delta(W)$ is a unit of $A$, where $\Delta(W)$ is the discriminant. Let $\Lambda \in A[X]$ be a polynomial such that the univariate division polynomial factors as $\mathrm{pre}\Psi_{p^k}(W) = \mathrm{pre}\Psi_{p^{k-1}}(W) \cdot \Lambda$, the exponent $k-1$ being truncated natural subtraction (so $k-1 = 0$ when $k = 0$). Let $x \in A$ be a root of $\Lambda$, i.e. $\Lambda(x) = 0$, and let $a$ be an integer not divisible by $p$. The conclusion is twofold: first, the value $\Psi^{\mathrm{sq}}_a(W)(x)$ at $x$ of the univariate polynomial whose quotient with $\Phi_a(W)$ gives the abscissa of $[a]P$ is a unit of $A$; and second, $\Lambda$ vanishes at $\Phi_a(W)(x) \cdot \Psi^{\mathrm{sq}}_a(W)(x)^{-1}$, the product being formed with `Ring.inverse`, which on the unit just exhibited is the genuine inverse. Thus the zero locus of $\Lambda$ in $A$ is carried into itself by the rational map $x \mapsto \Phi_a(x)/\Psi^{\mathrm{sq}}_a(x)$ describing multiplication by $a$ on abscissae.
--
--   Over a field this says that the set of abscissae of the points of exact order $p^k$ on an elliptic curve is permuted by multiplication by any integer prime to $p$; here it is stated over an arbitrary commutative ring in which $p\Delta$ is invertible, with $\Lambda$ any chosen primitive $p^k$-division polynomial. It is used in the study of the $p$-power level structures attached to $W$, being cited in the proof of [`ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot`](thm.html#ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eval_Phi_div_PsiSq_eq_zero_of_prePsi_pow_eq_mul_of_eval_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Polynomial

theorem WeierstrassCurve.eval_Phi_div_PsiSq_eq_zero_of_prePsi_pow_eq_mul_of_eval_eq_zero
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] (k : ℕ)
    (hpΔ : IsUnit ((p : A) * W.Δ)) {Λ : Polynomial A}
    (hΛ : W.preΨ (p ^ k) = W.preΨ (p ^ (k - 1)) * Λ)
    {x : A} (hx : Λ.eval x = 0) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    IsUnit ((W.ΨSq a).eval x) ∧
      Λ.eval ((W.Φ a).eval x * Ring.inverse ((W.ΨSq a).eval x)) = 0 := by sorry
