-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_proposition_3_1
-- name    : QAlgorithms.Papers.Independent.Information100.P50.proposition_3_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:53:09.333806+00:00
-- url     : https://prove2.me/theorems/17dd3c81-876c-42cc-b57d-ec048f763a83
-- title:
--   Proposition 3.1: For all CP Phi,Psi, Fhat(Phi,Psi)=lambda_min(Tr_Y(J(Phi)#J(Psi)))
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For any CP maps $\Phi,\Psi$, without trace preservation,
--
--   $$\widehat F(\Phi,\Psi)=\lambda_{\min}\!\left(\operatorname{Tr}_Y(J(\Phi)\#J(\Psi))\right).$$
--
--   Here $\#$ is the regularized geometric operator mean. The unsquared fidelity $\widehat F$ is the infimum of $\operatorname{tr}((\mathrm{id}_X\otimes\Phi)(\rho)\#(\mathrm{id}_X\otimes\Psi)(\rho))$ over the same density input $\rho$ on $X\otimes X$. This supplies the spectral formula for unnormalized CP maps.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 10, Proposition 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Proposition 3.1, source PDF p.10, for CP maps without trace normalization. -/
theorem proposition_3_1 {dx dy : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (Phi Psi : Lin dx dy) (hPhi : Entanglement.IsCompletelyPositive Phi)
    (hPsi : Entanglement.IsCompletelyPositive Psi) :
    geometricFidelity Phi Psi = minEigenvalue (traceLeft (geometricMean (choiMatrix Phi) (choiMatrix Psi))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
