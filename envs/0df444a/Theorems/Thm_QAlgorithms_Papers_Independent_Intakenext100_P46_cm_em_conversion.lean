-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_cm_em_conversion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.cm_em_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:00:51.77274+00:00
-- url     : https://prove2.me/theorems/3e758f70-6754-4fdb-b8cb-a416fd4beee2
-- title:
--   §2, Eq. (15): general CM/EM commutation relation and shared normal form
-- statement:
--   For a positive finite number of bosonic modes use $\Delta=\begin{pmatrix}0&I\\-I&0\end{pmatrix}$ and real symmetric covariances in the vacuum-$I/2$ convention. Every covariance with $\alpha-i\Delta/2>0$ has a unique finite exponential matrix $M$, and every real positive-definite $M$ has a unique physical covariance. Their common symplectic normal form obeys
--   $$\alpha=S\operatorname{diag}(\gamma,\gamma)S^T,\quad S^TMS=\operatorname{diag}(m,m),\quad \gamma_j=\tfrac12\coth(m_j/2),\quad m_j=\ln\frac{2\gamma_j+1}{2\gamma_j-1},$$
--   where $S$ is invertible and symplectic and $m_j>0$. Moreover
--   $$M\alpha\Delta^{-1}-\Delta^{-1}\alpha M=0.$$
--   The scalar functions apply in the normal chart. These conversions concern finite exponential matrices; the pure-mode endpoint is not assigned a real logarithmic value. The finite exponential matrix refers to the actual normalized Gibbs density: after a bounded unitary implementing the stated symplectic transformation, its number-basis weights are $\prod_j(1-e^{-m_j})e^{-m_j n_j}$. This operator meaning is part of the conclusion, alongside the covariance normal form.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 3, §2, Eq. (15): general CM/EM commutation relation and shared normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, PDF pp.2–3, (4),(5),(14),(15): mutually inverse finite-chart CM/EM
conversion, actual spectral Gibbs densities, shared normal form and commutation.
Pure modes are excluded only
from this computational chart, not from any state theorem. -/
theorem cm_em_conversion {I : Type} [Fintype I] [Nonempty I] :
    (∀ alpha : ModeMatrix I, StrictPhysical alpha → ∃! M : ModeMatrix I, GaussianEM alpha M) ∧
    (∀ M : ModeMatrix I, M.PosDef → ∃! alpha : ModeMatrix I, IsPhysicalCovariance alpha ∧ GaussianEM alpha M) ∧
    (∀ alpha M : ModeMatrix I, CMEM alpha M →
      GaussianEM alpha M ∧ M.PosDef ∧ M * alpha * (groupedCCR I)⁻¹ - (groupedCCR I)⁻¹ * alpha * M = 0 ∧
      ∃ (S : ModeMatrix I) (g m : I → ℝ), IsSymplecticMatrix S ∧
        (∀ j, 0 < m j ∧ g j = (1 / 2) * coth (m j / 2) ∧ m j = modeEM (g j)) ∧
        alpha = S * normalDiagonal g * S.transpose ∧
        S.transpose * M * S = normalDiagonal m) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
