-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_testingDivergence_positive
-- name    : QAlgorithms.Papers.Independent.Support50.P20.testingDivergence_positive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:32:01.053387+00:00
-- url     : https://prove2.me/theorems/d60371af-2a42-4da9-9ea9-f0202e0380a7
-- title:
--   Positivity and the identical-state zero-error case
-- statement:
--   Let $\rho,\sigma$ be arbitrary normalized positive trace-class operators on one complex Hilbert space, and let $0\le\epsilon<1$. With $D_H^\epsilon$ defined by the binary testing infimum in (1), in bits and allowing $+\infty$,
--
--   $$
--   D_H^\epsilon(\rho\|\sigma)\ge0,\qquad
--   \bigl(\rho=\sigma\ \text{and}\ \epsilon=0\bigr)\ \Longrightarrow\ D_H^\epsilon(\rho\|\sigma)=0.
--   $$
--
--   This supplies nonnegativity and the sufficient equality condition stated in the source. It makes no assertion that identical states have zero divergence at positive error tolerance.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 2, Property 1: positivity and identical-state zero-error equality

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2, Property 1: nonnegativity and the stated sufficient equality case.
No converse equality characterization is claimed. -/
theorem testingDivergence_positive {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : State b) (epsilon : ℝ) (hZero : 0 ≤ epsilon) (hOne : epsilon < 1) :
    0 ≤ hilbertTestingDivergence b epsilon rho.val.val sigma.val.val ∧
    (rho = sigma → epsilon = 0 →
      hilbertTestingDivergence b epsilon rho.val.val sigma.val.val = 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
