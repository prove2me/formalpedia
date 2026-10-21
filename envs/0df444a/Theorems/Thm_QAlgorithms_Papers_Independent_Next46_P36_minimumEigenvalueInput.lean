-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_minimumEigenvalueInput
-- name    : QAlgorithms.Papers.Independent.Next46.P36.minimumEigenvalueInput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:42:08.278991+00:00
-- url     : https://prove2.me/theorems/b524682a-b502-4712-a44d-57a32f505ed9
-- title:
--   Remark I: global optimum is the minimum cost-matrix eigenvalue
-- statement:
--   For a compact group, a finite nonempty canonical representation, normalized Haar prior and a real integrable generalized Holevo cost, let $C$ be the cost matrix of Theorem 2. There exist a real number $\lambda$ and a nonnegative real unit vector $v$ such that
--
--   $$Cv=\lambda v,\qquad \lambda\le w^TCw\ \text{for every real unit vector }w.$$
--
--   Thus $\lambda=\lambda_{\min}(C)$. For every choice of block unitaries, the canonical input with coefficients $v$ and the explicit rank-one covariant measurement attain the global minimum
--
--   $$R_{\rm global}=a_0+\lambda_{\min}(C).$$
--
--   The vector and eigenvalue are conclusions, not certificates assumed in the hypotheses. This reduces input optimization to a finite real eigenvalue problem, including a single-irrep representation.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 7, §III F Remark I

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.7 Remark I: an attained minimum eigenvalue and a nonnegative unit
minimizer, with no assumed eigenvalue or optimality certificate. -/
theorem minimumEigenvalueInput
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (K : IrrepCatalog G) (cost : G → G → ℝ) (hc : HolevoCost dg K cost) :
    ∃ lam : ℝ, ∃ v : S → ℝ,
      (∀ s, 0 ≤ v s) ∧ (∑ s, (v s) ^ 2) = 1 ∧
      (costMatrix D dg K cost).mulVec v = lam • v ∧
      (∀ w : S → ℝ, (∑ s, (w s) ^ 2) = 1 → lam ≤ quadraticCost (costMatrix D dg K cost) w) ∧
      ∀ W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ,
      ∃ M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G,
        M.reference = dg ∧
        (∀ g, M.density g = QAlgorithms.conjSuperop (canonicalAction D g)
          (QAlgorithms.pureDensity (likelihoodVector D (fun s => (v s : ℂ)) W))) ∧
        GlobalOptimal D dg cost (QAlgorithms.pureDensity (canonicalInput D (fun s => (v s : ℂ)) W)) M ∧
        risk D dg cost (QAlgorithms.pureDensity (canonicalInput D (fun s => (v s : ℂ)) W)) M =
          (fourierCoefficient dg cost (K.rep K.trivial)).re + lam := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
