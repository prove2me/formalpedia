-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_polynomial_family_rank_obstruction
-- name    : TranscendenceTheory.bounded_polynomial_family_rank_obstruction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T17:53:26.71579+00:00
-- url     : https://prove2.me/theorems/d8df8693-affa-4fb7-9c5e-061317c258bf
-- title:
--   Finite coefficient rank criterion for polynomial interpolation
-- statement:
--   Let $K$ be a field and let $J,I,H$ be finite index sets. Fix $d\ge0$ and polynomials $A_{ji},B_{jk}\in K[W]$, for $j\in J$, $i\in I$, and $k\in H$, all of degree at most $d$ (the zero polynomial is allowed).
--
--   Form matrices over $K$, with rows indexed by $(j,h)\in J\times\{0,\ldots,d\}$, by
--
--   $$\mathcal A_{(j,h),i}=[W^h]A_{ji},\qquad
--   \mathcal B_{(j,h),k}=[W^h]B_{jk}.$$
--
--   There is a right-hand side that cannot be represented by a constant linear combination of the columns of $A$ if and only if adjoining all right-hand-side columns increases rank:
--
--   $$
--   \left(\exists k\in H:\ \nexists u\in K^I\ \forall j\in J,
--   \ \sum_{i\in I}u_iA_{ji}(W)=B_{jk}(W)\right)
--   \quad\Longleftrightarrow\quad
--   \operatorname{rank}\mathcal A<\operatorname{rank}[\mathcal A\mid\mathcal B].
--   $$
--
--   The coefficient cutoff is exactly $d+1$ coefficients per polynomial equation. No nonemptiness assumptions, nonzero polynomial assumptions, or independence hypotheses on the columns are required. This criterion replaces a family of polynomial interpolation failures by a single finite matrix rank comparison.
-- source:
--   Derived finite coefficient rank criterion for the interpolation frontier https://prove2.me/theorems/4af1c4a0-3334-49b6-b559-e122c13d1774. Primary sources: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, LinearAlgebra/Matrix/Rank.lean, Matrix.rank_eq_finrank_span_cols, line 398: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Rank.lean#L398; LinearAlgebra/FiniteDimensional/Lemmas.lean, Submodule.finrank_lt_finrank_of_lt, line 235: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean#L235; Algebra/Polynomial/Degree/Operations.lean, Polynomial.coeff_eq_zero_of_natDegree_lt, line 85: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Degree/Operations.lean#L85. The complete theorem is derived here from finite-dimensional column spans and coefficient vanishing above degree; it is not a verbatim theorem from the mission paper. Mission context: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The connecting reduction preserves all hypotheses, witnesses, root conditions and numerical bounds, while bounding the exact branch coefficient indices by 2N|Z| and adjoining every right-hand-side column simultaneously. Both directions are checked in Lean. The uniform geometric estimate remains open.

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations

open scoped BigOperators

theorem TranscendenceTheory.bounded_polynomial_family_rank_obstruction
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (d : ℕ) (A : α → ι → Polynomial K) (B : α → κ → Polynomial K)
    (hA : ∀ a i, (A a i).natDegree ≤ d)
    (hB : ∀ a k, (B a k).natDegree ≤ d) :
    (∃ k, ¬ ∃ u : ι → K, ∀ a, ∑ i, Polynomial.C (u i) * A a i = B a k) ↔
      let Ac : Matrix (α × Fin (d + 1)) ι K := fun e i => (A e.1 i).coeff e.2.val
      let Bc : Matrix (α × Fin (d + 1)) κ K := fun e k => (B e.1 k).coeff e.2.val
      Ac.rank < (Matrix.fromCols Ac Bc).rank := by sorry
