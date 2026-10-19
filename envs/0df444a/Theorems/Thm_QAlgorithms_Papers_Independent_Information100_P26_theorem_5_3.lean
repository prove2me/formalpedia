-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_5_3
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_5_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:33:57.177396+00:00
-- url     : https://prove2.me/theorems/a5e20f96-2e3e-44b3-9b00-12a496188f1f
-- title:
--   Theorem 5.3: one continuous real weight on the compatible channel family
-- statement:
--   Let $A=\bigoplus_{k=1}^r\mathbb C I_{m_k}$ be the consecutive standard-coordinate scalar block algebra, where $r,m_k\ge1$ and $\sum_km_k=d$. Let $\Sigma_A$ be the unital channels $\tau$ for which $A\subseteq\operatorname{Fix}(\tau)\cap\operatorname{Range}(\tau)'$. There is one jointly continuous real function $\rho_A$ on $\Sigma_A\times U(A')\times U(A')$ satisfying, for every $\tau\in\Sigma_A$,
--   $$\tau=\int\!\int\rho_A(\tau,U,V)\beta_{U,V}\,dU\,dV,\qquad\rho_A(E_A,U,V)=1.$$
--   Both integrals use independent normalized Haar measures. This supplies weights uniformly over the whole compatible channel set. The formal function is extended off its stated domain, where no value or continuity is required.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 17, Theorem 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 5.3, PDF pp.17,18. An ambient function continuous on the source domain represents the same domain function; its off-domain values are unconstrained. -/
theorem theorem_5_3 {d : ℕ} (hd : 0 < d) (b : Blocks d)
    (mu : Measure (Unitary d)) (hmu : CommutantHaar (blockAlgebra b) mu) :
    ∃ rho : Map d × (Unitary d × Unitary d) → ℝ,
      ContinuousOn rho {z | UnitalChannel z.1 ∧ Compatible (blockAlgebra b) z.1 ∧
        InCommutant (blockAlgebra b) z.2.1 ∧ InCommutant (blockAlgebra b) z.2.2} ∧
      (∀ t : Map d, UnitalChannel t → Compatible (blockAlgebra b) t →
        t = weightedIntegral mu (fun U V => rho (t,(U,V)))) ∧
      (∀ U V : Unitary d, InCommutant (blockAlgebra b) U → InCommutant (blockAlgebra b) V →
        rho (expectation (blockAlgebra b),(U,V)) = 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
