-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_prefix_effective_equations
-- name    : WeierstrassEllipticZeta.triangular_prefix_effective_equations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T20:14:55.47788+00:00
-- url     : https://prove2.me/theorems/afbf8c51-88a4-4a40-8f29-f0948dc57423
-- title:
--   Sparse generators and colength bound for triangular ideal prefixes
-- statement:
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$, let $I\subseteq A$ be an ideal, and let $M\in\mathbb C[T]$ be monic. Let $r_1,r_2,r_3\in\mathbb C[T]$ and put $\phi(f)=f(T,r_1(T),r_2(T),r_3(T))$. Assume that, for every $f\in A$, membership $f\in I$ is equivalent to $M\mid\phi(f)$.
--
--   For any sequence $p_0,p_1,\ldots$ in $A$, define
--   $$J_s=I+(p_0,\ldots,p_{s-1}),\qquad
--   T_n=\{i<n:p_i\notin J_i\}.$$
--   Then, for every $n\geq0$,
--   $$J_n=I+(p_i:i\in T_n),\qquad
--   |T_n|+\dim_{\mathbb C}(A/J_n)\leq\deg M.$$
--   Thus the equations that change the ideal when first adjoined suffice to generate every prefix modulo $I$. Their number is bounded by the loss of quotient dimension. The assertion includes the empty prefix and the unit ideal.
-- source:
--   Derived commutative-algebra lemma associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This sparse-prefix lemma is derived here, not quoted from the article. Given a monic triangular time relation M and equations p_i, retain precisely those indices i at which p_i is absent from the preceding prefix ideal J_i. The retained equations generate each J_n modulo the original ideal, and their number plus the quotient dimension at n is at most deg M. The proof reuses the Proved prefix gcd recurrence; its supporting canonical update and hypersurface intersection length proofs are included in local kernel replay.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_prefix_effective_equations
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M.Monic)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (p : ℕ → MvPolynomial (Fin 4) ℂ) :
    let J := fun s : ℕ => I ⊔ Ideal.span (Set.range (fun i : Fin s => p i.val))
    ∀ n : ℕ,
      let T := (Finset.range n).filter (fun i => p i ∉ J i)
      J n = I ⊔ Ideal.span (p '' (T : Set ℕ)) ∧
      T.card + Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J n) ≤ M.natDegree := by sorry
