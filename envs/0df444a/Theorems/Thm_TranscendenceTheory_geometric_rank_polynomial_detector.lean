-- Prove2me | Theorems.Thm_TranscendenceTheory_geometric_rank_polynomial_detector
-- name    : TranscendenceTheory.geometric_rank_polynomial_detector
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T20:53:35.902455+00:00
-- url     : https://prove2.me/theorems/5cff5d16-fc41-457c-891b-d4f3d1c942a7
-- title:
--   Bounded polynomial detector for geometric interpolation ranks
-- statement:
--   Let $K$ be a field, let $J,I,H$ be finite index sets, and let $s\ge0$. Fix arbitrary polynomial families $V_{ji},B_{jk}\in K[W]$, with $j\in J$, $i\in I$, and $k\in H$.
--
--   For a candidate $c\in K$, put
--
--   $$R_{s,c}(W)=\sum_{r=0}^{s}(cW)^r.$$
--
--   Define matrices over $K$ with rows $(j,h)\in J\times\{0,\ldots,s\}$ by
--
--   $$\mathcal A_{(j,h),i}=[W^h]V_{ji}(W),\qquad
--   \mathcal B(c)_{(j,h),k}=[W^h]\big(R_{s,c}(W)B_{jk}(W)\big).$$
--
--   There exists a single polynomial $g\in K[T]$, of natural degree at most $s$, such that for every $c\in K$,
--
--   $$
--   \operatorname{rank}\mathcal A<\operatorname{rank}[\mathcal A\mid\mathcal B(c)]
--   \quad\Longleftrightarrow\quad g(c)\ne0.
--   $$
--
--   The bound on the detector's degree is independent of the number of equations, unknowns, or right-hand sides. There are no degree restrictions on V or B, and the finite index sets may be empty. The detector is allowed to be the zero polynomial; no nonvanishing assumption on it is made. This theorem replaces a parameterized matrix rank test by one bounded-degree polynomial nonvanishing test, uniformly in the candidate parameter.
-- source:
--   Derived bounded polynomial detector for the fixed-matrix frontier https://prove2.me/theorems/44933529-31f8-4d49-b734-f5df03752041. Primary sources at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474: RingTheory/PrincipalIdealDomain.lean, Ideal.span_singleton_generator and Submodule.IsPrincipal.mem_iff_generator_dvd, lines 90 and 135: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/PrincipalIdealDomain.lean#L90; LinearAlgebra/Dual/Lemmas.lean, Submodule.exists_dual_map_eq_bot_of_notMem, line 319: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Dual/Lemmas.lean#L319; Algebra/Polynomial/Degree/Domain.lean, Polynomial.natDegree_le_of_dvd, line 60: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Degree/Domain.lean#L60. The complete theorem is derived here by linear separation, a principal polynomial ideal and a coefficient expansion of the finite geometric series; it is not a verbatim theorem from the mission paper. Mission context: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The connecting reduction supplies valid bounded-degree detector families and replaces the two root-specific rank tests with polynomial nonvanishing. It preserves the original geometric hypotheses, witnesses, root conditions and numerical estimate. Both directions are checked in Lean. The geometric witness estimate remains open.

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem TranscendenceTheory.geometric_rank_polynomial_detector
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (s : ℕ) (V : α → ι → Polynomial K) (B : α → κ → Polynomial K) :
    ∃ g : Polynomial K, g.natDegree ≤ s ∧ ∀ c : K,
      let A₀ : Matrix (α × Fin (s + 1)) ι K := fun e i => (V e.1 i).coeff e.2.val
      let R : Polynomial K := ∑ r ∈ Finset.range (s + 1), (Polynomial.C c * Polynomial.X) ^ r
      let B₀ : Matrix (α × Fin (s + 1)) κ K := fun e k => (R * B e.1 k).coeff e.2.val
      (A₀.rank < (Matrix.fromCols A₀ B₀).rank) ↔ g.eval c ≠ 0 := by sorry
