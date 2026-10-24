-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_equivariantUnitary_coveringNumber
-- name    : QAlgorithms.Papers.Independent.Support50.P30.equivariantUnitary_coveringNumber
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:26:08.947875+00:00
-- url     : https://prove2.me/theorems/09e2278a-d2ba-418f-bfde-673453c207fb
-- title:
--   Theorem 5 (Operator-norm covering number)
-- statement:
--   For any $n\ge0$, let $V_n$ be the full family of unitary $n$-qubit matrices commuting with every qubit permutation. Use the spectral operator norm and internal covering centers in $V_n$. In the small-radius regime $0<\epsilon\le1$,
--
--   $$\mathcal N(V_n,\|\cdot\|_{\mathrm{op}},\epsilon)\le\left(\frac6\epsilon\right)^{2\binom{n+3}{3}}.$$
--
--   The exponent is twice the tetrahedral number. The radius restriction makes explicit the regime of the unitary-net estimate invoked by the proof; the printed theorem does not supply a radius domain. This bounds the full commuting family, for which blockwise net centers are internal.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 15, Theorem 5 (Operator-norm covering number)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.15, Theorem 5: exponent 2*Te_(n+1), internal centers in the full
commuting family, and spectral norm. PRINTED: the radius has no stated domain.
CHANGED: require 0 < epsilon <= 1, retaining the formula and family.
WHY: the invoked small-radius unitary-cover estimate applies in this regime;
for epsilon > 6 the printed bound is below one for a nonempty family.
The fixed cutoff 1 is a conservative small-radius choice, not a maximal domain. -/
theorem equivariantUnitary_coveringNumber (n : ℕ) (epsilon : ℝ≥0)
    (hpos : 0 < epsilon) (hsmall : epsilon ≤ 1) :
    (Metric.coveringNumber epsilon (unitaryFamily n) : ℝ≥0∞) ≤
      ENNReal.ofReal ((6 / (epsilon : ℝ)) ^ (2 * (n + 3).choose 3)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
