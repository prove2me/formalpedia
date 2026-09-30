-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_resultant_family_selection
-- name    : TranscendenceTheory.bounded_resultant_family_selection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T15:50:41.751528+00:00
-- url     : https://prove2.me/theorems/3b031712-890b-419a-bdb1-249ca5b2053f
-- title:
--   Bounded integer selection of a nonzero resultant from a finite family
-- statement:
--   Let $F$ be a nonzero polynomial in $\mathbb C[X][Y]$, and embed its coefficient ring into a characteristic-zero field $L$ in which $F$ splits. Let $H_0,\ldots,H_{k-1}$ be bivariate polynomials. Suppose that every root of $F$ in $L$ is avoided by at least one member of the family, that every $H_j$ has degree at most $s$ in $Y$, and that its coefficients have degree at most $b$ in $X$.
--
--   There is a natural number
--   $$0\le t\le (\deg_Y F)(k-1)$$
--   such that
--   $$Q(X,Y)=\sum_{j=0}^{k-1}t^jH_j(X,Y)$$
--   has nonzero resultant with $F$. Moreover, $Q$ still has degree at most $s$ in $Y$, and every coefficient of $Q$ has degree at most $b$ in $X$. The subtraction in the bound is truncated natural subtraction, so the assertion includes an empty family when its hypotheses permit one.
-- source:
--   Derived bounded-selection step for https://prove2.me/theorems/e228afdd-f183-4b04-ba4d-f76d7e7f01da. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. The selection lemma is a derived algebraic tool, not a claim to complete the paper zero estimate. Primary Lean sources: Mathlib Algebra/Polynomial/Roots.lean (root counts), RingTheory/Polynomial/Resultant/Basic.lean (product formula and Bezout identity), and Algebra/Polynomial/Degree/Operations.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. A finite family avoiding the roots of the first relation gives one resultant certificate with no increase in either polynomial degree bound.

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Complex.Basic

noncomputable section
open Polynomial
open scoped Classical

theorem TranscendenceTheory.bounded_resultant_family_selection
    (L : Type*) [Field L] [CharZero L]
    (φ : Polynomial ℂ →+* L) (hφ : Function.Injective φ)
    (F : Polynomial (Polynomial ℂ)) (k b s : ℕ)
    (H : Fin k → Polynomial (Polynomial ℂ))
    (hF : F ≠ 0) (hsplit : (F.map φ).Splits)
    (hroots : ∀ z ∈ (F.map φ).roots, ∃ j, (H j).eval₂ φ z ≠ 0)
    (hdegree : ∀ j, (H j).natDegree ≤ s)
    (hcoeff : ∀ j i, ((H j).coeff i).natDegree ≤ b) :
    ∃ a : ℕ, a ≤ F.natDegree * (k - 1) ∧
      let Q := ∑ j : Fin k, (a ^ j.val) • H j
      F.resultant Q ≠ 0 ∧ Q.natDegree ≤ s ∧
        ∀ i, (Q.coeff i).natDegree ≤ b := by sorry
