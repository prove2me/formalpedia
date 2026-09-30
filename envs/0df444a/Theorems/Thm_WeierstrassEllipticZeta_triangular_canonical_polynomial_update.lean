-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_canonical_polynomial_update
-- name    : WeierstrassEllipticZeta.triangular_canonical_polynomial_update
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T19:37:20.205621+00:00
-- url     : https://prove2.me/theorems/995310c4-94ad-4216-98f3-7f6dead3c409
-- title:
--   Canonical time polynomial after adjoining one equation: gcd and strict progress
-- statement:
--   Let $A=\mathbb C[X_0,X_1,X_2,X_3]$, and let
--   $\phi:A\to\mathbb C[T]$ be the substitution $X_0\mapsto T$,
--   $X_{i+1}\mapsto r_i(T)$ for three fixed complex polynomials $r_i$.
--   Suppose that $J$ is an ideal and $g$ is a monic polynomial such that
--   $f\in J$ if and only if $g\mid\phi(f)$ for every $f\in A$.
--
--   For any $p\in A$, put $h=\gcd(g,\phi(p))$ and $K=J+(p)$.
--   Then $h$ is monic, divides $g$, and is the unique monic polynomial
--   satisfying $f\in K\iff h\mid\phi(f)$ for all $f\in A$.
--   The quotient $A/K$ is finite dimensional and
--   $\dim_{\mathbb C}(A/K)=\deg h\leq\deg g$.
--   Moreover,
--
--   $$h=g\iff p\in J,$$
--   $$\deg h<\deg g\iff p\notin J,$$
--   $$\dim_{\mathbb C}(A/K)<\dim_{\mathbb C}(A/J)\iff p\notin J.$$
--
--   The case $J=A$ is included: then $g=1$ and adjoining an equation causes no drop.
-- source:
--   Derived commutative-algebra calculation associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This exact update theorem is derived here, not quoted from the article. If a triangular substitution identifies ideal membership with divisibility by a monic time polynomial g, adjoining p replaces g by the monic gcd of g and the substituted p. The proof gives the exact membership criterion, quotient dimension, uniqueness, and strict degree and dimension decrease exactly when p is absent from the original ideal. It reuses the Proved triangular hypersurface intersection length theorem and Mathlib ideal map/comap identities.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations

theorem WeierstrassEllipticZeta.triangular_canonical_polynomial_update
    (J : Ideal (MvPolynomial (Fin 4) ℂ)) (g : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hg : g.Monic)
    (hJ : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let h := gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
      let K := J ⊔ Ideal.span {p}
      h.Monic ∧ h ∣ g ∧
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ K ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = h.natDegree ∧
      h.natDegree ≤ g.natDegree ∧
      (h = g ↔ p ∈ J) ∧
      (h.natDegree < g.natDegree ↔ p ∉ J) ∧
      (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) <
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p ∉ J) ∧
      (∀ q : Polynomial ℂ, q.Monic →
        (∀ f : MvPolynomial (Fin 4) ℂ,
          f ∈ K ↔ q ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → q = h) := by sorry
