-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_sparse_bezout_certificate
-- name    : WeierstrassEllipticZeta.triangular_sparse_bezout_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T21:02:13.766895+00:00
-- url     : https://prove2.me/theorems/a783db6b-93ee-464b-bc23-f512b872b98c
-- title:
--   Sparse Bezout certificates with bounded time coefficients
-- statement:
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$, let $I\subseteq A$ be an ideal, and let $M\in\mathbb C[t]$ be monic. Choose $r_1,r_2,r_3\in\mathbb C[t]$ and set $\phi(f)=f(t,r_1(t),r_2(t),r_3(t))$. Assume that $f\in I$ if and only if $M\mid\phi(f)$ for every $f\in A$. Write $E(b)=b(x_0)$ and $d=\deg M$.
--
--   Given a sequence $p_0,p_1,\ldots$ in $A$, put $J_s=I+(p_0,\ldots,p_{s-1})$. Suppose $J_n=A$, and let $T=\{j<n:p_j\notin J_j\}$ be the indices of equations that changed the ideal when first adjoined. Then $|T|\leq d$, and there exist polynomials $b_j\in\mathbb C[t]$, indexed by $j\in T$, such that
--   $$\deg b_j<d,\qquad \deg_{\rm tot}E(b_j)\leq d-1,\qquad
--   1-\sum_{j\in T}E(b_j)p_j\in I.$$
--   For these same coefficients, whenever $D\in\mathbb N$ bounds the total degree of every retained $p_j$, one has
--   $$\deg_{\rm tot}\left(1-\sum_{j\in T}E(b_j)p_j\right)\leq(d-1)+D.$$
--   Here $d-1$ denotes truncated subtraction in $\mathbb N$, and the ordinary polynomial degree of zero is $-\infty$; total degree of the zero multivariate polynomial is zero. The assertion includes the empty prefix and $M=1$.
--
--   This gives a certificate of the unit ideal modulo $I$ whose number of terms and coefficient degrees are both bounded by the initial time relation.
-- source:
--   Derived commutative-algebra certificate associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here under an explicit triangular presentation; it is not quoted from the article. If a prefix generates the unit ideal modulo I, retain the equations that changed each preceding ideal. There are at most deg M such indices, and 1 has a certificate modulo I using only them with univariate time coefficients of degree below deg M. If the retained equations have total degree at most D, the certificate residual has total degree at most deg M-1+D. Reuses the Proved sparse-prefix and bounded-time coefficient lemmas; primary Mathlib tools include Ideal.mem_span_range_iff_exists_fun, Submodule.mem_sup and Fintype.sum_equiv.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.EquivFin

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_sparse_bezout_certificate
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M.Monic)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (p : ℕ → MvPolynomial (Fin 4) ℂ) (n : ℕ)
    (htop : I ⊔ Ideal.span (Set.range (fun i : Fin n => p i.val)) = ⊤) :
    let T := (Finset.range n).filter (fun j =>
      p j ∉ (I ⊔ Ideal.span (Set.range (fun i : Fin j => p i.val))))
    T.card ≤ M.natDegree ∧
    ∃ b : T → Polynomial ℂ,
      (∀ j : T, (b j).degree < (M.natDegree : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤
          M.natDegree - 1) ∧
      1 - ∑ j : T, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val ∈ I ∧
      ∀ D : ℕ, (∀ j : T, (p j.val).totalDegree ≤ D) →
        (1 - ∑ j : T, Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * p j.val).totalDegree ≤
          M.natDegree - 1 + D := by sorry
