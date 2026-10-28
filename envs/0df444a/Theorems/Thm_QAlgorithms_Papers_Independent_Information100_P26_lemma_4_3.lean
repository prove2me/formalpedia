-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_4_3
-- name    : QAlgorithms.Papers.Independent.Information100.P26.lemma_4_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:26:00.561982+00:00
-- url     : https://prove2.me/theorems/f313b90b-92e7-4b10-9aa0-3f01a1ca40f2
-- title:
--   Lemma 4.3: unweighted and covariant Haar averages
-- statement:
--   Let $d\ge2$ and let all unitary integrals use normalized Haar probability. Then
--   $$\int\!\int\beta_{U,V}\,dU\,dV=\delta_d,\qquad\delta_d\in\operatorname{MTD}(d).$$
--   For every $U\in U(d)$,
--   $$\int\beta_{V,VU}\,dV=\lambda(U)\operatorname{id}+(1-\lambda(U))\delta_d,\qquad\lambda(U)=\frac{\operatorname{Tr}_{\rm super}(\Delta_d\operatorname{Ad}_{U^*})-1}{d^2-1}.$$
--   In particular $\int\beta_{V,V}\,dV=\operatorname{id}/(d+1)+d\delta_d/(d+1)$. The trace in $\lambda$ is the trace of a superoperator on $M_d$. These identities identify the relevant Haar averages.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 14, Lemma 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Lemma 4.3, PDF pp.14,15. -/
theorem lemma_4_3 {d : ℕ} (hd : 2 ≤ d) (mu : Measure (Unitary d))
    (hmu : NormalizedHaar mu) :
    weightedIntegral mu (fun _ _ => 1) = depolarizing d ∧ MTD (depolarizing d) ∧
    (∀ U : Unitary d,
      let a : ℝ := ((Matrix.trace (dephasing d * ad (U : Mat d)ᴴ)).re - 1) /
        ((d : ℝ)^2-1)
      (∫ V : Unitary d, beta V (V * U) ∂mu) = a • (1 : Map d) + (1-a) • depolarizing d) ∧
    (∫ V : Unitary d, beta V V ∂mu) =
      (1 / ((d : ℝ)+1)) • (1 : Map d) + ((d : ℝ)/((d : ℝ)+1)) • depolarizing d := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
