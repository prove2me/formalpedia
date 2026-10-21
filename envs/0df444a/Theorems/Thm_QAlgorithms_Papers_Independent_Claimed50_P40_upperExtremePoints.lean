-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_upperExtremePoints
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.upperExtremePoints
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:51:46.878832+00:00
-- url     : https://prove2.me/theorems/19f24666-dbdb-4a2e-8788-b6de2c7051df
-- title:
--   Upper extreme points and permutation rate tuples
-- statement:
--   Fix a finite-dimensional classical-input multiple-access channel with $s\ge1$ finite nonempty sender alphabets and a product input law, giving channel state $\gamma$. Define
--   $$
--   \mathcal P=\left\{R\in\mathbb R_{\ge0}^s:\ \sum_{i\in J}R_i\le I_\gamma(X(J):YX(J^c))\text{ for every }J\subseteq[s]\right\}.
--   $$
--   Call a point upper extreme if it is an extreme point of $\mathcal P$ and is maximal in the coordinatewise order. For a permutation $\pi$ of $[s]$, define the rate tuple $R^\pi$ by
--   $$
--   R^\pi_{\pi(i)}=I_\gamma(X_{\pi(i)}:YX_{\pi(1)}\cdots X_{\pi(i-1)}),\qquad i=1,\ldots,s.
--   $$
--   Every upper extreme point of $\mathcal P$ equals $R^\pi$ for some permutation, and every $R^\pi$ belongs to $\mathcal P$. The first sender has no preceding classical register; all subset bounds include the empty and full subsets. These tuples describe the upper extreme points needed for the direct coding theorem.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 7, Appendix, Extremal points

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix, PDF p.7: every maximal extreme point is a permutation tuple, and every
permutation tuple is feasible. The converse is feasibility, not an invented boundary claim. -/
theorem upperExtremePoints {s : ℕ} (C : ClassicalChannel s) (P : InputLaw C.alphabet) :
    (∀ R : Fin s → ℝ, IsUpperExtreme (productLawRateRegion C P) R →
      ∃ pi : Equiv.Perm (Fin s), R = permutationRates C P pi) ∧
    (∀ pi : Equiv.Perm (Fin s), permutationRates C P pi ∈ productLawRateRegion C P) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
