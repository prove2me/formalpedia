-- Prove2me | Theorems.Thm_TranscendenceTheory_sparse_inconsistency_certificate
-- name    : TranscendenceTheory.sparse_inconsistency_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T17:01:42.627756+00:00
-- url     : https://prove2.me/theorems/51837f10-34e2-4b34-b6e0-30f37349f9f6
-- title:
--   Sparse normalized certificates of linear inconsistency
-- statement:
--   Let $K$ be a field, $I$ a finite set of unknowns, and $E$ an arbitrary set of equations. For coefficients $A_{e,i},B_e\in K$, the system
--
--   $$\sum_{i\in I}A_{e,i}u_i=B_e\qquad(e\in E)$$
--
--   has no solution in $K^I$ if and only if there exist an integer $r\le |I|+1$, selected equations $e_1,\ldots,e_r\in E$, and multipliers $\mu_1,\ldots,\mu_r\in K$ such that
--
--   $$\sum_{t=1}^r\mu_t A_{e_t,i}=0\quad(i\in I),\qquad\sum_{t=1}^r\mu_t B_{e_t}=1.$$
--
--   The equation set need not be finite. The selected equations may repeat; in particular, the bound also bounds the number of distinct equations used. There is no sign restriction on the multipliers. Empty equation and unknown sets are included.
--
--   This gives a normalized certificate of inconsistency whose size depends only on the number of unknowns. It applies to coefficient equations arising from polynomial interpolation over any field.
-- source:
--   Derived sparse linear-algebra alternative for the interpolation frontier https://prove2.me/theorems/0fa8049d-86af-4361-abe7-f37ded0bf6d0. Primary sources: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, LinearAlgebra/Dual/Lemmas.lean, Submodule.exists_dual_map_eq_bot_of_notMem, line 319: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Dual/Lemmas.lean#L319; LinearAlgebra/Dimension/StrongRankCondition.lean, Submodule.exists_fun_fin_finrank_span_eq, line 650: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean#L650; Algebra/Polynomial/Div.lean, Polynomial.X_pow_dvd_iff, line 44. The certificate theorem is derived here from linear separation and a basis of augmented rows; it is not a verbatim theorem from the mission paper. Mission context: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The connecting reduction treats the finite coefficient equations of the truncated branch and the arbitrary coefficient family of the exact branch. Separate Lean proofs verify both directions with the same hypotheses, witnesses, root conditions and numerical bound. The uniform geometric estimate remains open.

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Choose

open scoped BigOperators

theorem TranscendenceTheory.sparse_inconsistency_certificate
    (K ι α : Type*) [Field K] [Fintype ι]
    (A : α → ι → K) (B : α → K) :
    (¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a) ↔
      ∃ r : ℕ, r ≤ Fintype.card ι + 1 ∧
        ∃ a : Fin r → α, ∃ c : Fin r → K,
          (∀ i, ∑ j, c j * A (a j) i = 0) ∧
          ∑ j, c j * B (a j) = 1 := by sorry
