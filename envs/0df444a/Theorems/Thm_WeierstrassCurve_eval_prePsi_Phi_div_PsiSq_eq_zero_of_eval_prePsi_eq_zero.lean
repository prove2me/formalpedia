-- Prove2me | Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
-- name    : WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8466520c-d389-5899-a262-f8eae38b4de6
-- title:
--   Multiplication by a prime to p permutes ψₚ-roots
-- statement:
--   Let $A$ be a commutative ring and $W$ a Weierstrass curve over $A$, with discriminant $\Delta$ and division polynomials $\mathrm{pre}\Psi$, $\Psi^{\mathrm{sq}}$, $\Phi$ in the Mathlib normalisation, so that $\mathrm{pre}\Psi_n \in A[X]$ is the univariate division polynomial ($\psi_n$ itself for odd $n$), and $\Phi_n/\Psi^{\mathrm{sq}}_n$ is the abscissa of the $n$-th multiple of a point. Let $p$ be a prime with $p \neq 2$, and assume that $p \cdot \Delta$ is a unit of $A$. Let $x \in A$ be a root of $\mathrm{pre}\Psi_p$, i.e. $(\mathrm{pre}\Psi_p)(x) = 0$, and let $a$ be an integer not divisible by $p$. The assertion is twofold: first, $\Psi^{\mathrm{sq}}_a(x)$ is a unit of $A$; second, $\mathrm{pre}\Psi_p$ vanishes at $\Phi_a(x) \cdot \mathrm{inverse}(\Psi^{\mathrm{sq}}_a(x))$, where $\mathrm{inverse}$ is the ring inverse (which, by the first assertion, is the genuine inverse of $\Psi^{\mathrm{sq}}_a(x)$, so that the argument is the quotient $\Phi_a(x)/\Psi^{\mathrm{sq}}_a(x)$). Thus the abscissa map attached to multiplication by $a$ is defined at $x$ and carries roots of the $p$-division polynomial to roots of the $p$-division polynomial.
--
--   In geometric terms this says that multiplication by an integer $a$ prime to $p$ acts on the scheme of nonzero $p$-torsion points of $W$, written in division-polynomial coordinates; over a field it is the statement that $[a]$ permutes the nonzero $p$-torsion points. It is used in the treatment of level-$p$ structures on elliptic curves, in particular in the normal-form and vanishing results for $\Gamma_1$- and level-$p$-structure points on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpΔ : IsUnit ((p : A) * W.Δ)) {x : A} (hx : (W.preΨ p).eval x = 0) {a : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) :
    IsUnit ((W.ΨSq a).eval x) ∧
      (W.preΨ p).eval ((W.Φ a).eval x * Ring.inverse ((W.ΨSq a).eval x)) = 0 := by sorry
