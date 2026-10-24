-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P21_averageStateFidelity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P21.averageStateFidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:07:37.754448+00:00
-- url     : https://prove2.me/theorems/13803b40-d9d2-433d-b6a7-6caaec8f82be
-- title:
--   Average pure-state fidelity from channel entanglement fidelity
-- statement:
--   Let $d\ge1$. Let $V\mapsto R_V$ be an admissible integrable positive one-use instrument density, with deterministic two-comb integral, and let $U,V\in\mathrm{SU}(d)$ have independent normalized Haar reference laws. A pure input $\phi=|\psi\rangle\langle\psi|$ is independently sampled from the uniform probability measure on pure states. Let $\mathcal E_{V,U}$ denote the subnormalized output operation obtained by inserting $U$ into the instrument, and let $F$ be the average channel entanglement fidelity of Eq.(20). Define
--
--   $$
--   F'=\int d\phi\,dU\,dV\;\operatorname{Tr}[U\phi U^\dagger\,\mathcal E_{V,U}(\phi)].
--   $$
--
--   Then
--
--   $$
--   F'=\frac{d}{d+1}F+\frac1{d+1}.
--   $$
--
--   The subnormalized operation already supplies the outcome weight, so no second outcome-probability factor is present. This auxiliary identity includes the trivial one-dimensional family.
-- source:
--   Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation, arXiv:1006.5665v2, PDF p. 5, §IV A, following Eq.(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

/-- PDF p.5, following Eq.(20): uniformly averaged pure-state fidelity identity.
This auxiliary identity includes d=1, and uses the subnormalized operation exactly once. -/
theorem averageStateFidelity (d : ℕ) (hd : 0 < d) (H : HaarLaw d)
    (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : IsHaarCombInstrument H hd R) :
    averagePureFidelity H hd R =
      (d : ℝ)/((d : ℝ)+1) * channelScore H R + 1/((d : ℝ)+1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P21

end
