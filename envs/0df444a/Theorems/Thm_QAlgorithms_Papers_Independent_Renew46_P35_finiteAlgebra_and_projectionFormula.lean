-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_finiteAlgebra_and_projectionFormula
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.finiteAlgebra_and_projectionFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:08:07.250995+00:00
-- url     : https://prove2.me/theorems/a65ee852-0643-4fb0-a628-d071e5b5893f
-- title:
--   Lemma 13: finite unital algebra structure and all CP unital projections
-- statement:
--   Let $\mathcal A$ be a unital complex star subalgebra of $\mathcal B(H)$ for a nonzero finite-dimensional complex space $H$. There is one unitary decomposition into nonzero tensor blocks with
--
--   $$H=\bigoplus_jL_j\otimes R_j,\qquad\mathcal A=\bigoplus_j\mathcal B(L_j)\otimes1_{R_j}.$$
--
--   For every complex-linear completely positive unital idempotent map $P^*$ with exact range $\mathcal A$, there are normalized states $\omega_j$ on $R_j$, depending on $P^*$, such that
--
--   $$P^*(X)=\bigoplus_j\operatorname{Tr}_{R_j}\!\left(X_j(1_{L_j}\otimes\omega_j)\right)\otimes1_{R_j},\qquad X_j=\iota_j^*X\iota_j.$$
--
--   The operators $\iota_j$ are the orthogonal block inclusions. Multiplication by $1\otimes\omega_j$ occurs inside the partial trace, and the final factor is the identity operator. This describes every CP unital projection onto the algebra, with its decomposition chosen before the projection.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 8, Lemma 13: finite unital algebra structure and all CP unital projections

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

/-- PDF p.8, Lemma 13: one block decomposition for the algebra, then every CP unital
projection. The block states depend on the projection and the final tensor factor is I. -/
theorem finiteAlgebra_and_projectionFormula {H : Type*} [Fintype H] [Nonempty H]
    (a : StarSubalgebra ℂ (Matrix H H ℂ)) :
    ∃ d : MarkovTensorBlocks H, (∀ x, x ∈ a ↔ InBlockAlgebra d x) ∧
      ∀ p : Matrix H H ℂ →ₗ[ℂ] Matrix H H ℂ,
        Entanglement.IsCompletelyPositive p → p 1 = 1 → (∀ x, p (p x) = p x) →
        Set.range p = (a : Set (Matrix H H ℂ)) →
        ∃ omega : (j : Fin d.count) → Matrix (Fin (d.right j)) (Fin (d.right j)) ℂ,
          (∀ j, IsDensityMatrix (omega j)) ∧ ∀ x, p x = expectationFormula d omega x := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
