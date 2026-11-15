-- Prove2me | Theorems.Thm_Polynomial_abhyankar_isStandardEtale_finrank_and_algEquiv_laurentPolynomial
-- name    : Polynomial.abhyankar_isStandardEtale_finrank_and_algEquiv_laurentPolynomial
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T06:32:41.213273+00:00
-- url     : https://prove2.me/theorems/4a5fa6f1-581c-4b44-a527-c220e2a74c23
-- title:
--   The Abhyankar map $x \mapsto x^n + 1/x$ makes $\mathbb{G}_m$ a finite étale cover of $\mathbb{A}^1$ of degree $n+1$ when $n = 0$ in the base field
-- statement:
--   Let $F$ be a field and let $n \ge 1$ be an integer with $n = 0$ in $F$ (for example $n = p$ when $F$ has characteristic $p > 0$). In the polynomial ring $F[T][Y]$ put
--
--   $$f = Y^{n+1} - T\,Y + 1, \qquad B = F[T][Y]/(f).$$
--
--   Then:
--
--   1. $B$ is a standard étale $F[T]$-algebra (in Mathlib's sense), and in particular $B$ is étale over $F[T]$;
--   2. $B$ is a free and finitely generated $F[T]$-module of rank exactly $n + 1$;
--   3. there is an isomorphism of $F$-algebras $e : B \xrightarrow{\ \sim\ } F[x, x^{-1}]$ onto the ring of Laurent polynomials with
--
--   $$e(\bar Y) = x, \qquad e(\bar T) = x^n + x^{-1},$$
--
--   where $\bar Y$ and $\bar T$ are the classes of $Y$ and $T$ in $B$.
--
--   Geometrically, the morphism $\mathbb{G}_m \to \mathbb{A}^1$, $x \mapsto x^n + 1/x$, is finite étale of degree $n + 1$. The point is that $f' = (n+1)Y^n - T = Y^n - T$ because $n = 0$ in $F$, and $f' \cdot (-Y) + f = 1$, so $f'$ is a unit in $B$; the relation $Y(T - Y^n) = 1$ makes $\bar Y$ a unit with inverse $\bar T - \bar Y^n$, which gives the Laurent description. For $n = p$ this is the Abhyankar map that Katz uses to reduce statements about lisse sheaves on $\mathbb{G}_m$ to the affine line: in characteristic $p$ the affine line has connected finite étale covers of degree $> 1$ (no such cover exists in characteristic $0$).
--
--   **Formalization Note**: $F[T]$ is `Polynomial F` and $F[T][Y]$ is `Polynomial (Polynomial F)`, with $Y$ = `Polynomial.X` and $T$ = `Polynomial.C Polynomial.X`. The algebra $B$ is `AdjoinRoot f` (an $F[T]$-algebra through `AdjoinRoot.of f`, and an $F$-algebra through $F \to F[T]$); $\bar Y$ is `AdjoinRoot.root f` and $\bar T$ is `AdjoinRoot.of f Polynomial.X`. "Standard étale" is `Algebra.IsStandardEtale`, étale is `Algebra.Etale`, the rank is `Module.finrank (Polynomial F) B`, and $F[x, x^{-1}]$ is `LaurentPolynomial F` with $x^m$ = `LaurentPolynomial.T m` for $m \in \mathbb{Z}$. The hypotheses $n \ge 1$ and $(n : F) = 0$ are satisfiable exactly when $F$ has positive characteristic $p$ and $p \mid n$.
-- source:
--   N. M. Katz, "L-functions and monodromy: four lectures on Weil II", Advances in Mathematics 160 (2001), Lecture I, reduction to the affine line (the Abhyankar map $x \mapsto x^p + 1/x$ exhibits $\mathbb{G}_m$ as a finite étale cover of $\mathbb{A}^1$ of degree $p+1$)

import Mathlib

set_option autoImplicit false

theorem Polynomial.abhyankar_isStandardEtale_finrank_and_algEquiv_laurentPolynomial
    (F : Type*) [Field F] (n : ℕ) (hn : 1 ≤ n) (hp : (n : F) = 0) :
    Algebra.IsStandardEtale (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Algebra.Etale (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Module.Free (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Module.Finite (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) ∧
      Module.finrank (Polynomial F)
        (AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F))) = n + 1 ∧
      ∃ e : AdjoinRoot (Polynomial.X ^ (n + 1) - Polynomial.C Polynomial.X * Polynomial.X + 1 :
          Polynomial (Polynomial F)) ≃ₐ[F] LaurentPolynomial F,
        e (AdjoinRoot.root _) = LaurentPolynomial.T 1 ∧
          e (AdjoinRoot.of _ Polynomial.X) = LaurentPolynomial.T (n : ℤ) + LaurentPolynomial.T (-1) := by sorry
