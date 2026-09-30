-- Prove2me | Theorems.Thm_TranscendenceTheory_guarded_root_avoidance_bezout
-- name    : TranscendenceTheory.guarded_root_avoidance_bezout
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T21:54:34.904384+00:00
-- url     : https://prove2.me/theorems/9f4fe5da-b1a3-4c80-85ec-324ca0adc565
-- title:
--   Bounded Bezout certificates for guarded polynomial root avoidance
-- statement:
--   Let $K$ be an algebraically closed field and let $f,g,h\in K[T]$, with $n=\deg f>0$. Nonvanishing of $h$ at the common roots of $f$ and $g$ is equivalent to a bounded Bézout certificate:
--
--   $$
--   \bigl(\forall z\in K,\ f(z)=g(z)=0\Longrightarrow h(z)\ne0\bigr)
--   \quad\Longleftrightarrow\quad
--   \begin{gathered}
--   \exists A,B,C\in K[T],\quad Af+Bg+Ch=1,\\
--   \deg B<n,\qquad \deg C<n,\qquad
--   \deg A\le\max\{0,\deg g,\deg h\}.
--   \end{gathered}
--   $$
--
--   Zero polynomials are allowed for $g$, $h$, and the certificate coefficients. Repeated roots require no separability assumption. Taking $g=0$ gives a bounded certificate for nonvanishing at every root of $f$; taking $g$ to be a product of linear factors restricts the test to a specified finite spectrum.
--
--   This equivalence replaces a root-avoidance condition by finitely many coefficient equations with explicit degree bounds.
--
--   **Formalization Note** The statement uses natural degree, which assigns degree zero to the zero polynomial. Since $n>0$ and the bound for $A$ is nonnegative, this gives exactly the displayed certificate bounds.
-- source:
--   Derived bounded univariate Bezout criterion and equivalent reduction of https://prove2.me/theorems/68594e47-28c9-45bd-94ef-d0496f0252cf. Primary sources at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed, line 251, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L251; Polynomial.natDegree_mod_lt, line 423, and root_gcd_iff_root_left_right, lines 475-491, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/FieldDivision.lean#L423; EuclideanDomain.gcd_eq_gcd_ab, line 206, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/EuclideanDomain/Basic.lean#L206. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This certificate reduction is derived here, not a verbatim theorem from the paper.

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

theorem TranscendenceTheory.guarded_root_avoidance_bezout
    (K : Type*) [Field K] [IsAlgClosed K]
    (f g h : Polynomial K) (hf : f.natDegree ≠ 0) :
    (∀ z ∈ f.roots, g.eval z = 0 → h.eval z ≠ 0) ↔
      ∃ a b c : Polynomial K,
        a * f + b * g + c * h = 1 ∧
        b.natDegree < f.natDegree ∧ c.natDegree < f.natDegree ∧
        a.natDegree ≤ max g.natDegree h.natDegree := by sorry
