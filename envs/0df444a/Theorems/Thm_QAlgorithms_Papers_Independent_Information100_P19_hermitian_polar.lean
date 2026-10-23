-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_hermitian_polar
-- name    : QAlgorithms.Papers.Independent.Information100.P19.hermitian_polar
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:41:18.802495+00:00
-- url     : https://prove2.me/theorems/dd9ba89a-f94d-46db-9a88-ba3dd5c1d396
-- title:
--   Proposition 2.3
-- statement:
--   For $n\ge1$, let $M_n^{\rm all}$ be the closed conic hull of power-sum evaluation vectors of arbitrary finite real spectra of positive length. Then, for the standard coefficient pairing,
--   $$I_n^{\rm all}=(M_n^{\rm all})^\circ,$$
--   where the polar requires nonnegative pairings. The closure retains all dimension-free moment limits.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 10, Proposition 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 2.3; arXiv:2609.29471v1, PDF pp.10. -/
theorem hermitian_polar (n : ℕ) (hn : 1 ≤ n) : allCone n = spectralPolar (allMom n) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
