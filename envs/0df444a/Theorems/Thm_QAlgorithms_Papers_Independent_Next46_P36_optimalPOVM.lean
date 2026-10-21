-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_optimalPOVM
-- name    : QAlgorithms.Papers.Independent.Next46.P36.optimalPOVM
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:41:22.771989+00:00
-- url     : https://prove2.me/theorems/f59d7dd5-e6c2-485e-8e67-78abbfbb697d
-- title:
--   Theorem 2: optimal covariant POVM and sharp cost
-- statement:
--   Let $G$, its normalized Haar measure, its finite canonical representation, and a real integrable generalized Holevo cost satisfy the assumptions of Theorem 1. Fix arbitrary complex coefficients $c_\mu$ with $\sum_\mu|c_\mu|^2=1$ and arbitrary block unitaries $W_\mu$. For $\Psi=\bigoplus_\mu c_\mu\operatorname{vec}(W_\mu)/\sqrt{d_\mu}$ define
--
--   $$\eta=\bigoplus_\mu\sqrt{d_\mu}\,\operatorname{phase}(c_\mu)\operatorname{vec}(W_\mu),\qquad \operatorname{phase}(0)=1.$$
--
--   The seed $\Xi=|\eta\rangle\langle\eta|$ is positive, its continuous covariant density integrates to the identity, and its measurement minimizes risk over all admissible POVMs for this fixed input. Its exact risk is
--
--   $$R_{\rm opt}=a_0+\sum_{\mu,\nu}|c_\mu|C_{\mu\nu}|c_\nu|,\qquad C_{\mu\nu}=\sum_{\sigma\ne0}a_\sigma m_\sigma^{(\mu,\nu)}.$$
--
--   Here $m_\sigma^{(\mu,\nu)}$ is the actual multiplicity of $U^\sigma$ in $U^\mu\otimes\overline{U^\nu}$, defined as the complex dimension of the corresponding intertwiner space. Only finitely many terms contribute to each matrix entry. This is fixed-input optimality; the coefficients are not optimized in this theorem.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 6, Theorem 2, Eqs. (39)-(44)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF pp.6-7 Theorem 2, Eqs.(39)-(44): seed legality, fixed-input global
POVM optimality and the exact attained risk. Zero coefficients are allowed. -/
theorem optimalPOVM
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (K : IrrepCatalog G) (cost : G → G → ℝ) (hc : HolevoCost dg K cost)
    (c : S → ℂ) (hn : (∑ s, Complex.normSq (c s)) = 1)
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ) :
    QAlgorithms.IsState (canonicalInput D c W) ∧
    NormalizedSeed D dg (QAlgorithms.pureDensity (likelihoodVector D c W)) ∧
    ∃ M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G,
      M.reference = dg ∧
      (∀ g, M.density g = QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity (likelihoodVector D c W))) ∧
      CanonicalAdmissible D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) M ∧
      risk D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) M =
        (fourierCoefficient dg cost (K.rep K.trivial)).re +
          quadraticCost (costMatrix D dg K cost) (fun s => ‖c s‖) ∧
      (∀ N, CanonicalAdmissible D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) N →
        risk D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) M ≤
          risk D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) N) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
