-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_6_5
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_6_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:56:25.553417+00:00
-- url     : https://prove2.me/theorems/570822cb-dc54-48a9-adf1-3466ba66f8be
-- title:
--   Example 6.5: commutative peripheral space does not imply eventual EB
-- statement:
--   Let $d\ge2$ and $0<\lambda<1$. For $\tau=\lambda\operatorname{id}+(1-\lambda)\Delta_d$, the peripheral space is exactly the diagonal algebra and the only peripheral eigenvalue is $1$. Yet for every positive integer $n$,
--   $$\tau^n=\lambda^n\operatorname{id}+(1-\lambda^n)\Delta_d\quad\text{is not 2-copositive}.$$
--   Consequently $\tau$ is neither eventually 2-copositive nor eventually EB. Commutativity of the peripheral space alone is therefore insufficient.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 23, Example 6.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 6.5, PDF pp.23. -/
theorem example_6_5 {d : ℕ} (hd : 2 ≤ d) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let t := dephasingMixture d a
    UnitalChannel t ∧ peripheral t = diagonalSpace d ∧
    (∀ z : ℂ, ‖z‖ = 1 → (∃ X : Mat d, X ≠ 0 ∧ applyMap t X = z • X) → z = 1) ∧
    (∀ n : ℕ, 1 ≤ n → t^n = dephasingMixture d (a^n) ∧ ¬ TwoCopositive (t^n)) ∧
    ¬ Eventually TwoCopositive t ∧ ¬ Eventually EB t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
