-- Prove2me | Theorems.Thm_WeierstrassCurve_tate_isogeny_theorem_prime_to_char
-- name    : WeierstrassCurve.tate_isogeny_theorem_prime_to_char
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:05:25.983983+00:00
-- url     : https://prove2.me/theorems/9b26707e-2aa8-40c4-b35f-3120a53c416a
-- title:
--   Tate's isogeny theorem over finite fields, prime-to-$p$ form: ordinary elliptic curves with the same number of points are linked by isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$
-- statement:
--   Let $F$ be a finite field with $q$ elements and characteristic $p$, and let $E$ and $E'$ be elliptic curves over $F$, given by Weierstrass equations, with the same number of $F$-rational points:
--
--   $$\#E(F) = \#E'(F).$$
--
--   Suppose that $E$ is ordinary, that is, $p$ does not divide the trace of Frobenius $t = q + 1 - \#E(F)$. Then there are isogenies $u : E \to E'$ and $w : E' \to E$ defined over $F$ and an integer $N \ge 1$ prime to $p$ such that
--
--   $$w \circ u = [N],$$
--
--   multiplication by $N$ on $E$.
--
--   In terms of function fields, which is how the statement is formalized: let $F(E)$ and $F(E')$ be the function fields of $E$ and $E'$ over $F$, and let $x, y \in F(E)$ be the coordinate functions, so that $P = (x, y)$ is a point of $E$ over $F(E)$, the generic point. Then there are $F$-algebra homomorphisms $f : F(E') \to F(E)$ and $g : F(E) \to F(E')$ and a natural number $N$ with $N \ne 0$ in $F$ such that $f \circ g$, applied to the coordinates of $P$, gives the point $N P$ of $E$ over $F(E)$:
--
--   $$\big((f \circ g)(x),\, (f \circ g)(y)\big) = N \cdot (x, y) \quad \text{in } E(F(E)).$$
--
--   With $f = u^*$ and $g = w^*$ (pullback of functions) one has $f \circ g = (w \circ u)^*$, and $(w \circ u)^*$ sends $x, y$ to the coordinates of $(w \circ u)(P)$; since $F(E) = F(x, y)$, the displayed identity says exactly $f \circ g = [N]^*$, that is, $w \circ u = [N]$. Conversely, every $F$-algebra homomorphism $F(E') \to F(E)$ is the pullback $u^*$ of a unique nonconstant $F$-morphism $u : E \to E'$.
--
--   Role: Tate's theorem (1966) says that two elliptic curves over a finite field are isogenous over that field if and only if they have the same number of points. For ordinary curves Deuring's theory sharpens this: the endomorphism rings are orders of conductor prime to $p$ in an imaginary quadratic field in which $p$ splits, and an isogeny $u : E \to E'$ can be chosen of degree $N$ prime to $p$; its dual $w = \hat u$ satisfies $w \circ u = [N]$. This prime-to-$p$ form is the input to the Deuring-Waterhouse count of ordinary elliptic curves with a given trace of Frobenius by class numbers of imaginary quadratic orders, which together with the Eichler-Selberg trace formula gives the Ramanujan-Petersson bound for cusp forms of weight two.
--
--   **Formalization Note**: $F(E)$ is `W.toAffine.FunctionField`, the fraction field of the coordinate ring $F[x, y]/(\text{Weierstrass equation})$, and $\#E(F)$ is `Nat.card W.toAffine.Point`, which counts the affine points and the point at infinity. The generic point is `Point.some _ _ h` on the base change of `W` to its own function field, with coordinates the images in $F(E)$ of the classes of $x$ (`CoordinateRing.mk W.toAffine (C X)`) and $y$ (`CoordinateRing.mk W.toAffine X`); its nonsingularity `h` appears in the conclusion as an existential and always holds, since the curve is elliptic. `Point.map (f.comp g)` applies $f \circ g$ to the coordinates. Ordinarity is stated as $\neg\,((\mathrm{ringChar}\,F : \mathbb Z) \mid q + 1 - \#E(F))$. The universe of $F$ is fixed to `Type`. For $E = E'$ the conclusion holds with $f = g = \mathrm{id}$ and $N = 1$; the content is the case of non-isomorphic curves, where already the existence of an $F$-algebra homomorphism $F(E') \to F(E)$ is Tate's theorem.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1 (isogeny criterion: equal numbers of points); M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4 (ordinary elliptic curves: endomorphism orders of conductor prime to p, isogenies of degree prime to p); J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7 (dual isogeny, Tate's isogeny theorem)

import Mathlib

set_option autoImplicit false

theorem WeierstrassCurve.tate_isogeny_theorem_prime_to_char (F : Type) [Field F] [Fintype F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (hcard : Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point)
    (hord : ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)))) :
    ∃ (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ), (N : F) ≠ 0 ∧
      ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)),
        WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (f.comp g)
            (WeierstrassCurve.Affine.Point.some _ _ h) =
          N • WeierstrassCurve.Affine.Point.some _ _ h := by sorry
