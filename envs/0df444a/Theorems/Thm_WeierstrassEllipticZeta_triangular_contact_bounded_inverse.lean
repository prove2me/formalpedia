-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_contact_bounded_inverse
-- name    : WeierstrassEllipticZeta.triangular_contact_bounded_inverse
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T21:47:33.316704+00:00
-- url     : https://prove2.me/theorems/870d1dfd-5bb2-4865-a8c4-b0145fc71f9b
-- title:
--   Unique bounded time-polynomial inverses modulo finite contact ideals
-- statement:
--   Fix complex elliptic parameters $g_2,g_3$, a chart $c\in\{0,1\}$, a finite set $V\subset\mathbb C^4$, and contact orders $n(v)\in\mathbb N$. Write $A=\mathbb C[x_0,x_1,x_2,x_3]$, $I_v$ for the chart contact ideal of order $n(v)$ at $v$, and $I=\bigcap_{v\in V}I_v$.
--
--   Assume that $\ker(\operatorname{ev}_v)^{n(v)}\subseteq I_v$ for every $v$, and assume the explicit Chinese remainder property: every family $p_v\in A$ has a simultaneous representative $a\in A$ with $a-p_v\in I_v$.
--
--   Let $M\in\mathbb C[T]$ be monic and $r_1,r_2,r_3\in\mathbb C[T]$. Define $\phi:A\to\mathbb C[T]$ by substituting $(T,r_1,r_2,r_3)$ for $(x_0,x_1,x_2,x_3)$, and $E:\mathbb C[T]\to A$ by substituting $x_0$ for $T$. Assume the exact membership criterion
--   $$f\in I\quad\Longleftrightarrow\quad M\mid\phi(f).$$
--   Let $q\in A$ satisfy $q(v)\ne0$ whenever $n(v)>0$, and set $d=\deg M$.
--
--   There exists $b\in\mathbb C[T]$ such that
--   $$\deg b<d,\qquad \deg_{\rm tot}E(b)\le d-1,\qquad 1-E(b)q\in I,$$
--   and
--   $$\deg_{\rm tot}(1-E(b)q)\le d-1+\deg_{\rm tot}q.$$
--   This $b$ is unique among polynomials of degree less than $d$ satisfying the inverse congruence. Moreover, for every $f\in A$,
--   $$fq\in I\quad\Longleftrightarrow\quad f\in I,$$
--   and $I+(q)=A$.
--
--   The subtraction $d-1$ in natural-number degree bounds is truncated. Polynomial degree takes the value $-\infty$ at zero, while multivariate total degree of zero is zero. Empty contact sets, zero contact orders and $M=1$ are included. All contact and presentation assumptions above are explicit hypotheses of the formal statement.
-- source:
--   Derived finite contact-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. It is proved here under explicit contact-power, Chinese remainder and monic time-presentation hypotheses, not quoted from Theorem A.2. A polynomial nonzero at each positive-order contact point has a unique time-polynomial inverse of degree below deg M, an explicit residual degree bound and cancellation modulo the contact ideal. Reuses the Proved finite-contact Bezout certificate and bounded-time coefficient reduction. Uniqueness uses Mathlib Polynomial.eq_zero_of_dvd_of_degree_lt. No new definitions.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations

open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.triangular_contact_bounded_inverse
    (g₂ g₃ : ℂ) (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
    (hpower : ∀ v : V, RingHom.ker (MvPolynomial.eval v.val) ^ n v ≤
      extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (hcrt : ∀ p : V → MvPolynomial (Fin 4) ℂ,
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (M : Polynomial ℂ) (hM : M.Monic) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔
        M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (q : MvPolynomial (Fin 4) ℂ)
    (hq : ∀ v : V, 0 < n v → MvPolynomial.eval v.val q ≠ 0) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    ∃ b : Polynomial ℂ,
      b.degree < (M.natDegree : ℕ) ∧
      (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) b).totalDegree ≤
        M.natDegree - 1 ∧
      1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I ∧
      (1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q).totalDegree ≤
        M.natDegree - 1 + q.totalDegree ∧
      (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
        1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I → b' = b) ∧
      (∀ f : MvPolynomial (Fin 4) ℂ, f * q ∈ I ↔ f ∈ I) ∧
      I ⊔ Ideal.span {q} = ⊤ := by sorry
