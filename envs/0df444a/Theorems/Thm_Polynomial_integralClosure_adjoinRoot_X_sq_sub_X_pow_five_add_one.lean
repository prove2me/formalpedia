-- Prove2me | Theorems.Thm_Polynomial_integralClosure_adjoinRoot_X_sq_sub_X_pow_five_add_one
-- name    : Polynomial.integralClosure_adjoinRoot_X_sq_sub_X_pow_five_add_one
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T11:58:08.241355+00:00
-- url     : https://prove2.me/theorems/331812eb-d5fd-4fd7-a950-3cb35cb69df9
-- title:
--   Integral closure of $k[x]$ in the function field of $y^2 = x^5 + 1$ ($2, 5 \ne 0$ in $k$): it is $k[x] \oplus k[x]\,y = k[x, y]/(y^2 - x^5 - 1)$
-- statement:
--   Let $k$ be a field in which $2 \ne 0$ and $5 \ne 0$ (for instance $k = \mathbb F_q$ with $\gcd(q, 10) = 1$). The polynomial $Y^2 - (x^5 + 1)$ is irreducible over $k(x)$, and
--
--   $$F = k(x)[Y]/(Y^2 - x^5 - 1) = k(x)(y), \qquad y^2 = x^5 + 1,$$
--
--   is the function field of the genus-2 hyperelliptic curve $y^2 = x^5 + 1$. Let $\mathcal O \subset F$ be the integral closure of $k[x]$ in $F$ (the ring of regular functions on the affine curve). Then:
--
--   1. an element $z \in F$ is integral over $k[x]$ if and only if $z = a(x) + b(x)\,y$ with polynomials $a, b \in k[x]$; so $\mathcal O = k[x] \oplus k[x]\,y$;
--   2. the $k[x]$-algebra map $k[x][Y]/(Y^2 - x^5 - 1) \to F$, $Y \mapsto y$, is an isomorphism onto $\mathcal O$, i.e. $\mathcal O \cong k[x, y]/(y^2 - x^5 - 1)$;
--   3. consequently, for every commutative $k$-algebra $L$, evaluation at $(x, y)$ is a bijection
--
--   $$\mathrm{Hom}_{k\text{-alg}}(\mathcal O, L) \;\xrightarrow{\ \sim\ }\; \{(u, v) \in L^2 : v^2 = u^5 + 1\}, \qquad \psi \mapsto (\psi(x), \psi(y)).$$
--
--   Role: the affine model of the curve $y^2 = x^5 + 1$ over $\mathbb F_q$ needed to count its points: the $\mathbb F_{q^m}$-points of the affine curve are the $\mathbb F_q$-algebra maps $\mathcal O \to \mathbb F_{q^m}$. The proof uses the conjugation $y \mapsto -y$ (trace $2a$ and norm $a^2 - b^2(x^5+1)$ of $a + by$ lie in $k[x]$, which is integrally closed) and that $x^5 + 1$ is squarefree when $5 \ne 0$.
--
--   **Formalization Note**: $F$ is Mathlib's `AdjoinRoot p` for $p = Y^2 - C(x^5 + 1) \in k(x)[Y]$ (`k(x)` = `RatFunc k`), and $\mathcal O$ is `integralClosure k[X] (AdjoinRoot p)` (definitionally Mathlib's `FunctionField.ringOfIntegers`); $y$ is `AdjoinRoot.root p` and $x$ is the image of `X : k[X]`. The two polynomials are passed as variables `p`, `g` pinned by the equations `hp`, `hg` (only to shorten the statement). Part 2 asks for a `k[X]`-algebra isomorphism `AdjoinRoot g ≃ₐ[k[X]] integralClosure k[X] (AdjoinRoot p)` with $g = Y^2 - C(X^5 + 1) \in k[X][Y]$ sending `AdjoinRoot.root g` to $y$. Part 3 asks, for every commutative ring `L` with `[Algebra k L]` (in `Type`), for a bijection between `k`-algebra maps and the subtype `{q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1}` that sends `ψ` to `(ψ x, ψ y)` (stated for any elements `u`, `v` of $\mathcal O$ whose values in $F$ are $x$ and $y$). The hypotheses $2 \ne 0$, $5 \ne 0$ are needed for part 1: in characteristic 5, $x^5 + 1 = (x+1)^5$ and $y/(x+1)^2$ is integral (its square is $x + 1$); in characteristic 2, $(y+1)^2 = x^5$ and $(y+1)/x^2$ is integral (its square is $x$).
-- source:
--   Standard (integral closure of $k[x]$ in a quadratic extension $k(x)(\sqrt{f})$ with $f$ squarefree); see e.g. H. Stichtenoth, "Algebraic Function Fields and Codes", 2nd ed., GTM 254, Springer (2009), Section 6.2 (hyperelliptic function fields); used for the point count of $y^2 = x^5 + 1$ in the Ramanujan–Petersson (Deligne–Weil) formalization project

import Mathlib

set_option autoImplicit false

open Polynomial

theorem Polynomial.integralClosure_adjoinRoot_X_sq_sub_X_pow_five_add_one
    (k : Type) [Field k] (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (p : (RatFunc k)[X]) (hp : p = X ^ 2 - C (algebraMap k[X] (RatFunc k) (X ^ 5 + 1)))
    (g : k[X][X]) (hg : g = X ^ 2 - C (X ^ 5 + 1)) :
    (∀ z : AdjoinRoot p, IsIntegral k[X] z ↔
      ∃ a b : k[X], z = algebraMap k[X] (AdjoinRoot p) a + algebraMap k[X] (AdjoinRoot p) b * AdjoinRoot.root p) ∧
    (∃ e : AdjoinRoot g ≃ₐ[k[X]] integralClosure k[X] (AdjoinRoot p),
      (e (AdjoinRoot.root g) : AdjoinRoot p) = AdjoinRoot.root p) ∧
    ∀ (L : Type) [CommRing L] [Algebra k L],
      ∃ e : (integralClosure k[X] (AdjoinRoot p) →ₐ[k] L) ≃ {q : L × L // q.2 ^ 2 = q.1 ^ 5 + 1},
        ∀ (ψ : integralClosure k[X] (AdjoinRoot p) →ₐ[k] L) (u v : integralClosure k[X] (AdjoinRoot p)),
          (u : AdjoinRoot p) = algebraMap k[X] (AdjoinRoot p) X → (v : AdjoinRoot p) = AdjoinRoot.root p →
            (e ψ : L × L) = (ψ u, ψ v) := by sorry
