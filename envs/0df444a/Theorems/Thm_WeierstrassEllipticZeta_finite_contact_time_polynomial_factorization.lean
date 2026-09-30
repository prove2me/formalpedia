-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_contact_time_polynomial_factorization
-- name    : WeierstrassEllipticZeta.finite_contact_time_polynomial_factorization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T18:18:18.970519+00:00
-- url     : https://prove2.me/theorems/ba01d92e-7bd3-4dc8-aa90-0a25f03ffc1d
-- title:
--   Canonical time-polynomial factorization and roots from finite contact orders
-- statement:
--   Fix an elliptic-extension chart, with derivation $D$, a finite set
--   $V\subset\mathbb C^4$ and orders $n_v\in\mathbb N$. Write $t_v=v_0$ for
--   the time coordinate and set
--
--   $$A=\mathbb C[t,x_1,x_2,x_3],\qquad
--   I=\bigcap_{v\in V}C_v(n_v),\qquad
--   C_v(a)=\{p:D^jp(v)=0\text{ for }0\leq j<a\}.$$
--
--   Let $g\in\mathbb C[T]$ be monic. Assume it generates precisely the
--   univariate time relations in $I$, and has degree equal to the dimension
--   of the quotient:
--
--   $$q(t)\in I\quad\Longleftrightarrow\quad g\mid q
--   \qquad(q\in\mathbb C[T]),\qquad
--   \deg g=\dim_{\mathbb C}(A/I).$$
--
--   Then
--
--   $$g(T)=\prod_{v\in V}(T-t_v)^{n_v}.$$
--
--   In particular, for every $z\in\mathbb C$,
--
--   $$g(z)=0\quad\Longleftrightarrow\quad
--   \exists v\in V:\ n_v>0\ \text{and}\ z=t_v.$$
--
--   This identifies the canonical time relation explicitly from the contact
--   orders. Empty support and zero orders are allowed. The degree equality
--   is part of the hypotheses, including when time coordinates coincide.
-- source:
--   Derived time-polynomial calculation for the differential polynomial-ring method associated with Senthil Kumar K (2026), Appendix A introductory paragraphs and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This exact factorization is derived here, not quoted from the article. A monic polynomial generating the time relations of a finite contact ideal and having degree equal to the full quotient dimension is the product of the time linear factors raised to the contact orders. Its roots are exactly the time coordinates with positive order. Reuses the Proved contact-ideal structure and quotient-dimension theorems. Maximal-ideal powers give membership of the product, and equal degrees give equality of monic polynomials. The dimension equality is an explicit hypothesis, including for coincident time coordinates.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.finite_contact_time_polynomial_factorization (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) (g : Polynomial ℂ) (hg : g.Monic)
    (htime : ∀ q : Polynomial ℂ,
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈
        (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔ g ∣ q)
    (hdegree : g.natDegree = Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v))) :
    g = (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v) ∧
      ∀ z : ℂ, g.eval z = 0 ↔ ∃ v : V, 0 < n v ∧ z = v.val 0 := by sorry
