-- Prove2me | Theorems.Thm_WeierstrassCurve_natCard_point_eq_of_isogeny_prime_to_char
-- name    : WeierstrassCurve.natCard_point_eq_of_isogeny_prime_to_char
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:46:23.469873+00:00
-- url     : https://prove2.me/theorems/4b06d795-eab2-4688-85d5-8237142cccfb
-- title:
--   Isogenous elliptic curves over a finite field have the same number of points (converse of Tate's isogeny theorem, prime-to-$p$ form)
-- statement:
--   Let $F$ be a finite field of characteristic $p$, and let $E$ and $E'$ be elliptic curves over $F$, given by Weierstrass equations. Suppose there are isogenies $u : E \to E'$ and $w : E' \to E$ defined over $F$ and an integer $N$ prime to $p$ such that
--
--   $$w \circ u = [N],$$
--
--   multiplication by $N$ on $E$. Then $E$ and $E'$ have the same number of $F$-rational points:
--
--   $$\#E(F) = \#E'(F),$$
--
--   and hence the same trace of Frobenius $q + 1 - \#E(F)$, where $q = \#F$.
--
--   In terms of function fields, which is how the statement is formalized: let $F(E)$ and $F(E')$ be the function fields of $E$ and $E'$ over $F$, and let $x, y \in F(E)$ be the coordinate functions, so that $P = (x, y)$ is a point of $E$ over $F(E)$, the generic point. The hypothesis is that there are $F$-algebra homomorphisms $f : F(E') \to F(E)$ and $g : F(E) \to F(E')$ and a natural number $N$ with $N \ne 0$ in $F$ such that $f \circ g$, applied to the coordinates of $P$, gives the point $N P$ of $E$ over $F(E)$:
--
--   $$\big((f \circ g)(x),\, (f \circ g)(y)\big) = N \cdot (x, y) \quad \text{in } E(F(E)).$$
--
--   With $f = u^*$ and $g = w^*$ (pullback of functions) one has $f \circ g = (w \circ u)^*$, which sends $x, y$ to the coordinates of $(w \circ u)(P)$; since $F(E) = F(x, y)$, the displayed identity says exactly $w \circ u = [N]$. Every $F$-algebra homomorphism $F(E') \to F(E)$ is the pullback $u^*$ of a unique nonconstant $F$-morphism $u : E \to E'$. The conclusion is $\#E(F) = \#E'(F)$.
--
--   Together with the statement `WeierstrassCurve.tate_isogeny_theorem_prime_to_char` (ordinary curves with the same number of points admit such data), this makes Tate's theorem in its prime-to-$p$ form an equivalence for ordinary curves.
--
--   Proof idea: over an algebraic closure $\bar F$, $u$ is a group homomorphism $E(\bar F) \to E'(\bar F)$ commuting with the $q$-power Frobenius $\pi$, and $u \ne 0$ because $w \circ u = [N]$ is nonzero for $p \nmid N$. A nonzero isogeny has finite kernel, and $u \circ (1 - \pi_E) = (1 - \pi_{E'}) \circ u$; comparing degrees, $\deg(1 - \pi_E) = \deg(1 - \pi_{E'})$, that is, $\#E(F) = \#\ker(1 - \pi_E) = \#\ker(1 - \pi_{E'}) = \#E'(F)$ (both $1 - \pi$ are separable).
--
--   **Formalization Note**: $F$ is a field with `[Fintype F]`; $E$, $E'$ are `W W' : WeierstrassCurve F` with `[W.IsElliptic]`, `[W'.IsElliptic]`. $\#E(F)$ is `Nat.card W.toAffine.Point` (Mathlib's type of nonsingular affine points together with the point at infinity). The function field $F(E)$ is `W.toAffine.FunctionField`, the coordinate functions are the images of `Polynomial.C Polynomial.X` ($x$) and `Polynomial.X` ($y$) under `CoordinateRing.mk` followed by `algebraMap` into the function field, the generic point is `Point.some _ _ h` on the base change `W.baseChange W.toAffine.FunctionField` (the hypothesis packages the nonsingularity proof `h` with the identity), and $f \circ g$ acts on points by `WeierstrassCurve.Affine.Point.map (f.comp g)`. The hypothesis has exactly the shape of the conclusion of `WeierstrassCurve.tate_isogeny_theorem_prime_to_char`.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Exercise 5.4 and Theorem V.2.3.1

import Mathlib

set_option autoImplicit false

theorem WeierstrassCurve.natCard_point_eq_of_isogeny_prime_to_char (F : Type) [Field F] [Fintype F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ) (hN : (N : F) ≠ 0)
    (hfg : ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)),
        WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (f.comp g)
            (WeierstrassCurve.Affine.Point.some _ _ h) =
          N • WeierstrassCurve.Affine.Point.some _ _ h) :
    Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point := by
  sorry
