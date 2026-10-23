-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_strongest_interpolation_pair
-- name    : QAlgorithms.Papers.Independent.Information100.P19.strongest_interpolation_pair
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:58:16.429287+00:00
-- url     : https://prove2.me/theorems/82d21840-8ede-4618-aa72-e689fbb11a0c
-- title:
--   Proposition 5.11
-- statement:
--   For every nonzero finite real vector $s$, the maximum over integers $1\le a<b$ of
--   $$\frac{\|s\|_{2a}^{2a(2b-1)/(b-a)}}{\|s\|_{2b}^{2b(2a-1)/(b-a)}}$$
--   is attained at $(a,b)=(1,2)$. No normalization of $s$ is required. The positive index restriction follows the interpolation derivation and avoids an undefined zero-order norm.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 34, Proposition 5.11

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 5.11; arXiv:2609.29471v1, PDF pp.34. -/
theorem strongest_interpolation_pair (N : ℕ) (s : Fin N → ℝ) (hs : s≠0) :
    ∀ a b : ℕ, 1≤a → a<b →
      interpolationRatio s a b ≤ interpolationRatio s 1 2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
