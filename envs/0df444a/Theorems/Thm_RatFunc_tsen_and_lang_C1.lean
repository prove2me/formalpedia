-- Prove2me | Theorems.Thm_RatFunc_tsen_and_lang_C1
-- name    : RatFunc.tsen_and_lang_C1
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T01:30:44.053866+00:00
-- url     : https://prove2.me/theorems/bfce20b1-100d-4815-9dfe-05df6a314f87
-- title:
--   Tsen's theorem: every algebraic extension of $k(t)$, $k$ algebraically closed, is $C_1$; Lang: algebraic extensions of $C_1$ fields are $C_1$, with surjective norms
-- statement:
--   Call a field $F$ **$C_1$** if every polynomial $f \in F[x_1, \dots, x_n]$ (for any $n$) whose total degree is smaller than the number of variables, $\deg f < n$, and whose constant term is $0$ has a nontrivial zero:
--
--   $$\exists\, x \in F^n,\ x \ne 0,\ f(x) = 0.$$
--
--   Let $k$ be an algebraically closed field and let $L$ be an algebraic extension of the rational function field $k(t)$. Then:
--
--   1. (**Tsen**) $L$ is $C_1$;
--   2. (**Lang**) for every field $K$ that is $C_1$ and every algebraic extension $E/K$:
--      (a) $E$ is $C_1$, and
--      (b) if $E/K$ is finite, the norm map $N_{E/K} : E \to K$ is surjective.
--
--   In particular, for every finite extension $L'/L$ the norm $N_{L'/L} : L' \to L$ is surjective, so the Brauer group of $L$ vanishes; this applies to the function field of every curve over $k$.
--
--   Role: $C_1$ (quasi-algebraically closed) fields are the fields of cohomological dimension $\le 1$ in the theory of Galois cohomology. Tsen's theorem (1933) is the input that makes $\mathrm{Gal}(\bar K/K)$ have cohomological dimension $\le 1$ for the function field $K$ of a curve over an algebraically closed field.
--
--   **Formalization Note**: $k(t)$ is `RatFunc k`. The $C_1$ property is written out in each place: `f.totalDegree < n` and `MvPolynomial.constantCoeff f = 0` imply `∃ x : Fin n → F, x ≠ 0 ∧ MvPolynomial.eval x f = 0`. This is the strong form of $C_1$ (Lang's "quasi-algebraically closed", for all polynomials without constant term); for a form of degree $d$ with $0 < d < n$ it gives the classical statement that the form has a nontrivial zero. $N_{E/K}$ is `Algebra.norm K`, and finiteness of $E/K$ is `Module.Finite K E`. Part 2 holds for arbitrary fields $K$ and $E$ (in any universe), not only for extensions of $k(t)$.
-- source:
--   C. Tsen, Divisionsalgebren ueber Funktionenkoerpern, Nachr. Ges. Wiss. Goettingen, Math.-Phys. Kl. (1933), 335-339; S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785; J.-P. Serre, Galois Cohomology, Springer 1997, doi:10.1007/978-3-642-59141-9, Chapter II, Section 3

import Mathlib

set_option autoImplicit false

theorem RatFunc.tsen_and_lang_C1
    (k : Type*) [Field k] [IsAlgClosed k] (L : Type*) [Field L] [Algebra (RatFunc k) L]
    [Algebra.IsAlgebraic (RatFunc k) L] :
    (∀ (n : ℕ) (f : MvPolynomial (Fin n) L), f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
        ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) ∧
      ∀ (K : Type*) (E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsAlgebraic K E],
        (∀ (n : ℕ) (f : MvPolynomial (Fin n) K), f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
            ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) →
          (∀ (n : ℕ) (f : MvPolynomial (Fin n) E), f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
              ∃ x : Fin n → E, x ≠ 0 ∧ MvPolynomial.eval x f = 0) ∧
            (Module.Finite K E → Function.Surjective (Algebra.norm K : E → K)) := by sorry
