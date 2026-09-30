-- Prove2me | Theorems.Thm_TranscendenceTheory_truncated_geometric_rank_equivalence
-- name    : TranscendenceTheory.truncated_geometric_rank_equivalence
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T20:17:16.808306+00:00
-- url     : https://prove2.me/theorems/d873805b-2245-47d6-b852-8a60f099e848
-- title:
--   Geometric-series equivalence of truncated interpolation rank tests
-- statement:
--   Let $K$ be a field, let $J,I,H$ be finite index sets, let $s\ge0$, and let $c\in K$. Take arbitrary polynomial families $V_{ji},B_{jk}\in K[W]$ for $j\in J$, $i\in I$, and $k\in H$. Define
--
--   $$R_{s,c}(W)=\sum_{r=0}^{s}(cW)^r.$$
--
--   All matrices below have rows indexed by $(j,h)\in J\times\{0,\ldots,s\}$. Define matrices with $I$ columns by
--
--   $$\mathcal A_{(j,h),i}=[W^h]\big((1-cW)V_{ji}(W)\big),\qquad
--   \mathcal A^0_{(j,h),i}=[W^h]V_{ji}(W),$$
--
--   and matrices with $H$ columns by
--
--   $$\mathcal B_{(j,h),k}=[W^h]B_{jk}(W),\qquad
--   \mathcal B^0_{(j,h),k}=[W^h]\big(R_{s,c}(W)B_{jk}(W)\big).$$
--
--   Then the two augmented-rank tests are equivalent:
--
--   $$
--   \operatorname{rank}\mathcal A<\operatorname{rank}[\mathcal A\mid\mathcal B]
--   \quad\Longleftrightarrow\quad
--   \operatorname{rank}\mathcal A^0<\operatorname{rank}[\mathcal A^0\mid\mathcal B^0].
--   $$
--
--   The result has no degree restrictions or nonemptiness assumptions and includes $c=0$ and $s=0$. It removes the candidate parameter $c$ from the left-hand matrix when the input families are fixed. The parameter then enters only through the explicitly specified finite geometric transformation of the right-hand sides.
-- source:
--   Derived explicit geometric-series reduction for the interpolation frontier https://prove2.me/theorems/37582c08-3ae4-434c-b78d-a8083d516763. Primary sources at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: Algebra/Ring/GeomSum.lean, geom_sum_mul_neg, line 240: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Ring/GeomSum.lean#L240; Algebra/Polynomial/Div.lean, Polynomial.X_pow_dvd_iff, line 44: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L44; LinearAlgebra/Matrix/Rank.lean, Matrix.rank_eq_finrank_span_cols, line 398: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Rank.lean#L398. The complete theorem is derived here from a finite geometric inverse modulo X^(s+1) and the finite column-span criterion; it is not a verbatim theorem from the mission paper. Mission context: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The connecting reduction removes the candidate parameter from both left-hand matrices, retaining the same row counts, fields, geometric hypotheses, witnesses, root conditions and numerical bound. Both directions are checked in Lean. The uniform geometric estimate remains open.

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem TranscendenceTheory.truncated_geometric_rank_equivalence
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (s : ℕ) (c : K) (V : α → ι → Polynomial K) (B : α → κ → Polynomial K) :
    let G : Polynomial K := ∑ k ∈ Finset.range (s + 1), (Polynomial.C c * Polynomial.X) ^ k
    let Ac : Matrix (α × Fin (s + 1)) ι K := fun e i =>
      ((1 - Polynomial.C c * Polynomial.X) * V e.1 i).coeff e.2.val
    let Bc : Matrix (α × Fin (s + 1)) κ K := fun e k => (B e.1 k).coeff e.2.val
    let A₀ : Matrix (α × Fin (s + 1)) ι K := fun e i => (V e.1 i).coeff e.2.val
    let B₀ : Matrix (α × Fin (s + 1)) κ K := fun e k => (G * B e.1 k).coeff e.2.val
    (Ac.rank < (Matrix.fromCols Ac Bc).rank) ↔
      A₀.rank < (Matrix.fromCols A₀ B₀).rank := by sorry
