-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_twist_natCard_point_add_natCard_point_eq
-- name    : WeierstrassCurve.exists_twist_natCard_point_add_natCard_point_eq
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:13:35.892881+00:00
-- url     : https://prove2.me/theorems/024b1867-83e2-5dec-ac55-7ccf3a7e9554
-- title:
--   Quadratic twists over $\mathbb{F}_q$: every elliptic curve $E/\mathbb{F}_q$ has a twist $E'$ with $\#E(\mathbb{F}_q) + \#E'(\mathbb{F}_q) = 2q + 2$
-- statement:
--   Let $\mathbb{F}_q$ be a finite field with $q$ elements, of any characteristic (including $2$ and $3$), and let $E$ be an elliptic curve over $\mathbb{F}_q$, given by a general Weierstrass equation
--
--   $$E : y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$$
--
--   with nonzero discriminant. Then there is a Weierstrass curve $E'$ over $\mathbb{F}_q$ that is a twist of $E$, meaning that $E'$ is isomorphic to $E$ over an algebraic closure $\overline{\mathbb{F}}_q$ by an admissible change of variables $(x, y) \mapsto (u^2x + r,\ u^3y + u^2sx + t)$ with $u, r, s, t \in \overline{\mathbb{F}}_q$, $u \neq 0$, such that
--
--   $$\#E(\mathbb{F}_q) + \#E'(\mathbb{F}_q) = 2q + 2.$$
--
--   Equivalently, the Frobenius traces $a(E) = q + 1 - \#E(\mathbb{F}_q)$ satisfy $a(E') = -a(E)$. The curve $E'$ is the quadratic twist of $E$: for odd $q$, after completing the square $E$ becomes $y^2 = f(x)$ and $E'$ is $dy^2 = f(x)$ with $d$ a nonsquare in $\mathbb{F}_q$; in characteristic $2$ it is the Artin-Schreier twist. The statement holds for every $j$-invariant, including $j = 0$ and $j = 1728$, where $E$ also has quartic or sextic twists. For $j \neq 0, 1728$ the curves over $\mathbb{F}_q$ with a given $j$-invariant form exactly two $\mathbb{F}_q$-isomorphism classes, $E$ and $E'$, so the identity says that their Frobenius traces are $\pm a$; this is the sign symmetry used when Frobenius traces are summed over the $j$-line.
--
--   **Formalization Note**: $E$ is `W : WeierstrassCurve F` with `[W.IsElliptic]` (the discriminant is a unit, i.e. nonzero), and $q$ is `Fintype.card F`. `Nat.card W.toAffine.Point` counts the nonsingular affine $\mathbb{F}_q$-points together with the point at infinity, so it is $\#E(\mathbb{F}_q)$. The twist condition is the existence of `C : WeierstrassCurve.VariableChange (AlgebraicClosure F)` with `C • W.baseChange (AlgebraicClosure F) = W'.baseChange (AlgebraicClosure F)`, an isomorphism of Weierstrass models over $\overline{\mathbb{F}}_q$; it forces $E'$ to be elliptic as well, so no hypothesis on $E'$ is needed.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapter X (twists) and Chapter V (elliptic curves over finite fields)

import Mathlib

set_option autoImplicit false

theorem WeierstrassCurve.exists_twist_natCard_point_add_natCard_point_eq
    {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic] :
    ∃ W' : WeierstrassCurve F,
      (∃ C : WeierstrassCurve.VariableChange (AlgebraicClosure F),
        C • W.baseChange (AlgebraicClosure F) = W'.baseChange (AlgebraicClosure F)) ∧
      Nat.card W.toAffine.Point + Nat.card W'.toAffine.Point = 2 * Fintype.card F + 2 := by
  sorry
