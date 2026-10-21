-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_coherentInformation_iff_reversal
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.coherentInformation_iff_reversal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:03:19.868313+00:00
-- url     : https://prove2.me/theorems/3dc07ec6-1915-4168-92ed-4b0da3565d24
-- title:
--   Example 8: perfect channel reversal iff coherent information equals input entropy
-- statement:
--   Let $\sigma$ be a density on a nonzero finite-dimensional space $H$, and let $|\psi\rangle\in A\otimes H$ be any normalized purification, so $\operatorname{Tr}_A|\psi\rangle\langle\psi|=\sigma$. Let $\phi:\mathcal B(H)\to\mathcal B(K)$ be CPTP. Define the coherent information in bits by $I_c(\sigma,\phi)=S(\phi(\sigma))-S((\operatorname{id}_A\otimes\phi)(|\psi\rangle\langle\psi|))$. Then
--
--   $$\exists R\text{ CPTP}:\ (\operatorname{id}_A\otimes R\phi)(|\psi\rangle\langle\psi|)=|\psi\rangle\langle\psi|\quad\Longleftrightarrow\quad I_c(\sigma,\phi)=S(\sigma).$$
--
--   The reference $A$ and purification are arbitrary. This perfect reversal criterion is credited by the source to Schumacher and Nielsen [18].
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 5, Example 8: perfect channel reversal iff coherent information equals input entropy

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

/-- PDF pp.5–6, Example 8, credit [18]: reversal iff coherent information equals input entropy.
The normalized purification is arbitrary, including its reference dimension. -/
theorem coherentInformation_iff_reversal {A H K : Type*}
    [Fintype A] [Fintype H] [Fintype K] [Nonempty A] [Nonempty H] [Nonempty K]
    (s : Matrix H H ℂ) (hs : IsDensityMatrix s)
    (psi : EuclideanSpace ℂ (A × H)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = s) (f : Superop H K) (hf : IsChannel f) :
    (∃ r : Superop K H, IsChannel r ∧
      idTensorSuperop (R := A) (r ∘ f) (pureDensity psi) = pureDensity psi) ↔
      vnEntropy (f s) - vnEntropy (idTensorSuperop (R := A) f (pureDensity psi)) =
        vnEntropy s := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
