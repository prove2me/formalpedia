-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_bezout_clear_denominators
-- name    : TranscendenceTheory.bounded_bezout_clear_denominators
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T23:42:28.90598+00:00
-- url     : https://prove2.me/theorems/1b650b1d-6a15-49d1-9504-3ea7e8bf2269
-- title:
--   Clearing denominators in bounded Bezout certificates
-- statement:
--   Let $R$ be an integral domain and let $K$ be its field of fractions, with embedding $\iota:R\hookrightarrow K$. Fix $f,g,h\in R[Y]$ and natural-number bounds $a,b,c$. Write $\delta$ for natural degree, with $\delta(0)=0$.
--
--   The following bounded certificate over the fraction field exists:
--
--   $$
--   \begin{gathered}
--   \exists U,V,W\in K[Y],\qquad
--   U\iota_*f+V\iota_*g+W\iota_*h=1,\\
--   \delta(V)<b,\qquad\delta(W)<c,\qquad\delta(U)\le a
--   \end{gathered}
--   $$
--
--   if and only if there is a certificate over the domain with a nonzero scalar right-hand side:
--
--   $$
--   \begin{gathered}
--   \exists d\in R\setminus\{0\},\quad\exists u,v,w\in R[Y],\qquad
--   uf+vg+wh=d,\\
--   \delta(v)<b,\qquad\delta(w)<c,\qquad\delta(u)\le a.
--   \end{gathered}
--   $$
--
--   On the right, $d$ is regarded as a constant polynomial in $Y$. The bounds refer to degree in $Y$, and they are unchanged by clearing denominators. The polynomials $f,g,h$ may be zero. No Noetherian or unique-factorization hypothesis on $R$ is required. If $b=0$ or $c=0$, both existence assertions are false under the stated natural-degree convention.
--
--   For $R=\mathbb C[T]$, this replaces rational-function coefficients by polynomial coefficients and a nonzero polynomial $d(T)$ on the right. It does not assert a bound on the $T$-degree of $d$ or of the new certificate coefficients.
-- source:
--   Derived bounded denominator-clearing equivalence and equivalent reduction of https://prove2.me/theorems/298e7d03-29ff-47f8-abd8-4d02bc0cd1fc. Primary sources at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: IsLocalization.integerNormalization, integerNormalization_spec, and integerNormalization_support, lines 48-59, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Localization/Integral.lean#L48; Polynomial.natDegree_le_iff_coeff_eq_zero, line 78, natDegree_C_mul_le, line 95, and natDegree_map_eq_of_injective, line 293, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Degree/Lemmas.lean#L78. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. This equivalence is derived here, not a verbatim theorem from the paper.

import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination

theorem TranscendenceTheory.bounded_bezout_clear_denominators
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f g h : Polynomial R) (a b c : ℕ) :
    (∃ u v w : Polynomial K,
      u * f.map (algebraMap R K) + v * g.map (algebraMap R K) +
          w * h.map (algebraMap R K) = 1 ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) ↔
    (∃ d : R, d ≠ 0 ∧ ∃ u v w : Polynomial R,
      u * f + v * g + w * h = Polynomial.C d ∧
      v.natDegree < b ∧ w.natDegree < c ∧ u.natDegree ≤ a) := by sorry
