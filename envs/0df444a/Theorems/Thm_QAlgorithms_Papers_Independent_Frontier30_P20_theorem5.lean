-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem5
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:35:38.423442+00:00
-- url     : https://prove2.me/theorems/8fc160e7-5639-4bb0-9bca-905c8b547c07
-- title:
--   Theorem 5 (Kraus rank two maps)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Every completely positive map $T$ with Kraus rank exactly two has real, nonnegative determinant. The same holds for every finite composition of such maps:
--
--   $$\det(T_1\cdots T_m)\ge0.$$
--
--   No factor is required to preserve trace; the empty composition is the identity.
--
--   This prevents rank-two CP factors from producing negative determinants.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 8, Theorem 5 (Kraus rank two maps)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 5, PDF p.8: exact rank two, no trace-preservation assumption, and all finite products. -/
theorem theorem5 {d : ℕ} (hd : 0 < d) :
    (∀ T : Super d, QAlgorithms.Entanglement.IsCompletelyPositive T.toLinearMap → krausRank T = 2 →
      (complexDet T).im = 0 ∧ 0 ≤ determinant T) ∧
    (∀ factors : List (Super d), (∀ T ∈ factors, QAlgorithms.Entanglement.IsCompletelyPositive T.toLinearMap ∧ krausRank T = 2) →
      (complexDet factors.prod).im = 0 ∧ 0 ≤ determinant factors.prod) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
