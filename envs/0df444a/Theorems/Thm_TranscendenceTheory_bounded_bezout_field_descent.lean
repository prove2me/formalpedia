-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_bezout_field_descent
-- name    : TranscendenceTheory.bounded_bezout_field_descent
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T22:53:24.042994+00:00
-- url     : https://prove2.me/theorems/a734d628-1bdd-46f4-9b4c-e61dc04d2020
-- title:
--   Bounded Bezout certificates descend along any field extension
-- statement:
--   Let $L/K$ be any field extension, with coefficient embedding $\iota:K\hookrightarrow L$. Let $f,g,h\in K[Y]$ and let $a,b,c$ be natural numbers. Write $\delta(P)$ for natural degree, so that $\delta(0)=0$.
--
--   A Bézout certificate with these prescribed degree bounds exists over $L$ if and only if one exists over $K$:
--
--   $$
--   \begin{aligned}
--   &\exists U,V,W\in L[Y],\quad
--    U\iota_*f+V\iota_*g+W\iota_*h=1,\\
--   &\hspace{35mm}\delta(V)<b,\quad\delta(W)<c,\quad\delta(U)\le a
--   \end{aligned}
--   $$
--
--   is equivalent to
--
--   $$
--   \begin{aligned}
--   &\exists u,v,w\in K[Y],\quad uf+vg+wh=1,\\
--   &\hspace{35mm}\delta(v)<b,\quad\delta(w)<c,\quad\delta(u)\le a.
--   \end{aligned}
--   $$
--
--   There is no algebraicity, finite-dimensionality, characteristic, or algebraic-closedness assumption on the extension. The polynomials may be zero. If $b=0$ or $c=0$, both bounded existence assertions are false under the stated natural-degree convention.
--
--   This result permits bounded polynomial certificates obtained over an algebraic closure to be sought over the original coefficient field, with exactly the same degree limits.
-- source:
--   Derived degree-preserving field descent and equivalent reduction of https://prove2.me/theorems/cf950c6d-5cac-4881-ba87-355667b6efe6. Primary sources at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: PolynomialModule.equivPolynomial and PolynomialModule.map, lines 260-317, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Module/Basic.lean#L260; Module.Projective.exists_dual_eq_one, line 213, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Dual/Lemmas.lean#L213; Polynomial.natDegree_le_iff_coeff_eq_zero, line 78, and natDegree_map_eq_of_injective, line 293, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Degree/Lemmas.lean#L78. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This descent reduction is derived here, not a verbatim theorem from the paper.

import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

theorem TranscendenceTheory.bounded_bezout_field_descent
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f g h : Polynomial K) (a b c : ℕ) :
    (∃ u v w : Polynomial L,
      u * f.map (algebraMap K L) + v * g.map (algebraMap K L) +
          w * h.map (algebraMap K L) = 1 ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) ↔
    (∃ u v w : Polynomial K,
      u * f + v * g + w * h = 1 ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) := by sorry
