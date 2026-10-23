-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_5_11
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_5_11
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:55:50.478069+00:00
-- url     : https://prove2.me/theorems/6dd7823a-76ba-4c78-b7c9-77253ca7d6e1
-- title:
--   Example 5.11: fixed diagonal algebra does not imply range commutation
-- statement:
--   Let $d\ge2$, $0<\lambda<1$, and let $A$ be the standard diagonal algebra, so $E_A=\Delta_d$. The map $\tau=\lambda\operatorname{id}+(1-\lambda)\Delta_d$ is a unital channel fixing $A$ pointwise, but it is neither 2-copositive nor MTD, and $\operatorname{Range}(\tau)\not\subseteq A'$. More precisely,
--   $$((\tau\circ T)\otimes\operatorname{id}_2)\begin{pmatrix}E_{11}&E_{12}\E_{21}&E_{22}\end{pmatrix}=\begin{pmatrix}E_{11}&\lambda E_{21}\\lambda E_{12}&E_{22}\end{pmatrix},$$
--   and this output has eigenvalue $-\lambda<0$. This counterexample shows why fixed points alone do not supply the range condition.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 21, Example 5.11

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 5.11, PDF pp.21. -/
theorem example_5_11 {d : ℕ} (hd : 2 ≤ d) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let t := dephasingMixture d a
    expectation (diagonalSpace d) = dephasing d ∧ UnitalChannel t ∧ Fixes t (diagonalSpace d) ∧
    ¬ TwoCopositive t ∧ ¬ MTD t ∧
    ¬ (∀ X : Mat d, applyMap t X ∈ commutant (diagonalSpace d : Set (Mat d))) ∧
    amplify (t * transposition d) 2
      (fun p q => bellTest d p * conj (bellTest d q)) = negativeTestImage d a ∧
    (∃ w : Fin d × Fin 2 → ℂ, w ≠ 0 ∧
      (negativeTestImage d a).mulVec w = (-(a : ℂ)) • w) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
