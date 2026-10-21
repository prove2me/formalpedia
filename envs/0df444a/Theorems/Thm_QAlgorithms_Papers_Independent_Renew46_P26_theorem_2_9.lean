-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_theorem_2_9
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.theorem_2_9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:49:45.539883+00:00
-- url     : https://prove2.me/theorems/45b99718-95a4-4a20-8c4b-126f7da00fc3
-- title:
--   Theorem 2.9
-- statement:
--   For every $n\geq1$, every finite-dimensional nonzero irreducible complex $S_n$-module $V$, and every irreducible complex $S_{n-1}$-module $W$, restriction along the last-letter inclusion satisfies
--
--   $$\dim_{\mathbb C}\operatorname{Hom}_{S_{n-1}}(W,\operatorname{Res}V)\in\{0,1\}.$$
--
--   The multiplicity is the dimension of an actual equivariant Hom space. This establishes simple branching throughout the tower.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 13, Theorem 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 2.9 (PDF p.13). Every adjacent restriction in the actual tower has
multiplicities 0 or 1; the Hom dimensions are natural numbers. -/
theorem theorem_2_9 (n : ℕ) : HasSimpleRestriction (prefixInclusion (Nat.le_succ n)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
