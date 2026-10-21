-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_theorem_2_8
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.theorem_2_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:49:23.887539+00:00
-- url     : https://prove2.me/theorems/33cdabca-51b0-44f0-958b-158d1fcc2671
-- title:
--   Theorem 2.8
-- statement:
--   For $n\geq1$, with the last-letter inclusion of $S_{n-1}$ and $X_n=\sum_{j<n}(j,n)$, the full centralizer is
--
--   $$Z(\mathbb C[S_n],\mathbb C[S_{n-1}])=\langle Z(n-1),X_n\rangle.$$
--
--   Both containments are asserted. This describes the entire centralizer rather than only proving it commutative.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 12, Theorem 2.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 2.8 (PDF p.12). Equality, including both generation directions. -/
theorem theorem_2_8 (n : ℕ) :
    Subalgebra.centralizer ℂ (prefixAlgebra (Nat.le_succ n) : Set (SymmetricAlgebra (n + 1))) =
      Algebra.adjoin ℂ ((prefixCenter (Nat.le_succ n) : Set (SymmetricAlgebra (n + 1))) ∪
        {yjm (Fin.last n)}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
