-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotent_fiber_calculus
-- name    : WeierstrassEllipticZeta.polynomial_nilpotent_fiber_calculus
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T23:34:01.174318+00:00
-- url     : https://prove2.me/theorems/fa1ea04c-1e39-42e4-ab16-6cbcf610edae
-- title:
--   Polynomial evaluation at a nilpotent perturbation of a scalar
-- statement:
--   Let $K$ be a field, $A$ a nonzero commutative ring, and $\phi:K\to A$ a unital ring homomorphism. Let $x\in A$, $z\in K$ and $d\in\mathbb N$ satisfy
--   $$
--   (x-\phi(z))^d=0.
--   $$
--   For every polynomial $q\in K[T]$, write $q_\phi(x)$ for evaluation at $x$ with coefficients mapped through $\phi$. Then
--   $$
--   \bigl(q_\phi(x)-\phi(q(z))\bigr)^d=0,
--   $$
--   and
--   $$
--   q_\phi(x)\in A^\times\quad\Longleftrightarrow\quad q(z)\ne0,
--   \qquad
--   q_\phi(x)\text{ is nilpotent}\quad\Longleftrightarrow\quad q(z)=0.
--   $$
--   Thus polynomial evaluation preserves the supplied nilpotence bound for a perturbation of a scalar, and the scalar polynomial value determines invertibility and nilpotence. Nontriviality of $A$ is part of the hypotheses. No finite-dimensionality assumption is needed.
-- source:
--   Derived algebra lemma, proved here from Polynomial.X_sub_C_dvd_sub_C_eval in Mathlib, Algebra/Polynomial/Div.lean, lines 602-603, and nilpotent-unit lemmas in RingTheory/Nilpotent/Basic.lean, lines 83-103, at revision 0df444a360eaa60ab8c11dca51a86af692955474. Sources: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L602-L603 and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Nilpotent/Basic.lean#L83-L103. Polynomial evaluation preserves the given nilpotence exponent of a scalar perturbation; its value is a unit exactly when the scalar evaluation is nonzero, and nilpotent exactly when that evaluation is zero. This supporting lemma for the Senthil Kumar mission is not quoted from the article. The target ring is nontrivial. No new definitions or platform theorem dependencies.

import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Nilpotent.Basic

theorem WeierstrassEllipticZeta.polynomial_nilpotent_fiber_calculus
    (K A : Type*) [Field K] [CommRing A] [Nontrivial A]
    (φ : K →+* A) (x : A) (z : K) (d : ℕ) (hx : (x - φ z) ^ d = 0)
    (q : Polynomial K) :
    (q.eval₂ φ x - φ (q.eval z)) ^ d = 0 ∧
      (IsUnit (q.eval₂ φ x) ↔ q.eval z ≠ 0) ∧
      (IsNilpotent (q.eval₂ φ x) ↔ q.eval z = 0) := by sorry
