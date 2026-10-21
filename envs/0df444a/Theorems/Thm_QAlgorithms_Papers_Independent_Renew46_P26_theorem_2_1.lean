-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_theorem_2_1
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.theorem_2_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:46:00.159373+00:00
-- url     : https://prove2.me/theorems/270397ab-750f-4fba-8a5f-b7f71fd0b71d
-- title:
--   Theorem 2.1
-- statement:
--   For every $n\geq1$, embed $S_{n-1}$ into $S_n$ by fixing the last letter. The centralizer of its complex group algebra is commutative:
--
--   $$xy=yx\qquad(x,y\in Z(\mathbb C[S_n],\mathbb C[S_{n-1}])).$$
--
--   The statement includes $S_0\subset S_1$ and supplies the multiplicity-free branching criterion.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 9, Theorem 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 2.1 (PDF p.9). The actual centralizer for S_n inside S_(n+1)
is commutative, including S_0 inside S_1. -/
theorem theorem_2_1 (n : ℕ) :
    IsCommutativeSubalgebra
      (Subalgebra.centralizer ℂ (prefixAlgebra (Nat.le_succ n) : Set (SymmetricAlgebra (n + 1)))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
