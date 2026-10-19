-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_crossingOrder
-- name    : QAlgorithms.Papers.Independent.Information100.P39.crossingOrder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:18:44.396441+00:00
-- url     : https://prove2.me/theorems/82023987-fc1a-4a60-b911-89f4e590b7a8
-- title:
--   Unnumbered crossing-strength ordering, Eq.(41)
-- statement:
--   Fix a finite stabilizer code and a family of normalized independent-event Pauli laws parametrized by $p$ in a closed real interval $[a,b]$. For every positive integer order and infinity, suppose a point $p_c^{(r)}\in[a,b]$ is a zero of the actual encoded coherent information, which is strictly positive below that point and strictly negative above it within the interval. Then
--
--   $$p_c^{(r)}\le p_c^{(s)}\qquad(1\le r\le s\le\infty).$$
--
--   The hypotheses specify the crossings and their sign patterns. This orders existing transition strengths without asserting existence of a crossing or monotonicity in the noise parameter.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 5, Unnumbered crossing-strength ordering, Eq.(41)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF p.5, Eq.(41): crossing existence and signs are hypotheses; order
monotonicity alone does not assert a transition. The infinite order is included. -/
theorem crossingOrder {N k : ℕ} (C : StabilizerCode N k)
    (a b : ℝ) (nu : ℝ → PauliLabel N → ℝ)
    (hnu : ∀ p ∈ Set.Icc a b, Learning.IsDistribution (nu p))
    (hind : ∀ p ∈ Set.Icc a b, HasIndependentEvents (nu p))
    (pc : Order → ℝ)
    (hcross : ∀ r : Order, 1 ≤ r → PositiveNegativeCrossing
      (parameterInformation C a b nu hnu r) a b (pc r)) :
    ∀ r s : Order, 1 ≤ r → r ≤ s → pc r ≤ pc s := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
