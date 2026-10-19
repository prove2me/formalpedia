-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_proposition_5_2
-- name    : QAlgorithms.Papers.Independent.Information100.P26.proposition_5_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:33:20.868558+00:00
-- url     : https://prove2.me/theorems/b8156aec-ccca-4a37-b6aa-269a22c71d26
-- title:
--   Proposition 5.2: commutant Haar averages and conditional expectations
-- statement:
--   Let $A\subseteq M_d$ be a unital $C^*$-subalgebra, $d\ge1$, and let $E_A$ be its unique trace-preserving conditional expectation, equivalently its Hilbert–Schmidt orthogonal projection. With independent normalized Haar measure on $U(A')$,
--   $$\int\!\int\beta_{U,V}\,dU\,dV=E_A\Delta_d E_A.$$
--   If every element of $A$ is diagonal in the fixed standard basis, the integral equals $E_A$. For every commutative $A$, including non-diagonal ones, $E_A$ is MTD. Only this last assertion is transported by unitary covariance.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 17, Proposition 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Proposition 5.2, PDF pp.17. -/
theorem proposition_5_2 {d : ℕ} (hd : 0 < d) (A : Submodule ℂ (Mat d)) (hA : CStar A)
    (mu : Measure (Unitary d)) (hmu : CommutantHaar A mu) :
    weightedIntegral mu (fun _ _ => 1) = expectation A * dephasing d * expectation A ∧
    ((∀ X ∈ A, ∀ i j : Fin d, i ≠ j → X i j = 0) →
      weightedIntegral mu (fun _ _ => 1) = expectation A) ∧
    (Commutative A → MTD (expectation A)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
