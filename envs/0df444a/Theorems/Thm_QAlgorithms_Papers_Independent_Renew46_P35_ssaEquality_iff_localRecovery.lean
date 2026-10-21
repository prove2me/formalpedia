-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_ssaEquality_iff_localRecovery
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.ssaEquality_iff_localRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:01:38.569661+00:00
-- url     : https://prove2.me/theorems/49c6d8ea-f19d-4007-bf7a-d06e8b5a1fb2
-- title:
--   Section V, unnumbered equation (11): local Markov recovery characterization
-- statement:
--   Let $\rho_{ABC}$ be a density operator on nonzero finite-dimensional complex spaces, with computed marginals. Define $I(A:C\mid B)=S(\rho_{AB})+S(\rho_{BC})-S(\rho_{ABC})-S(\rho_B)$ in bits. Then
--
--   $$I(A:C\mid B)=0\quad\Longleftrightarrow\quad\exists R:\mathcal B(B)\to\mathcal B(B\otimes C)\text{ CPTP},\ (\operatorname{id}_A\otimes R)(\rho_{AB})=\rho_{ABC}.$$
--
--   The recovery map may depend on the state and acts on $B$ alone. This is the source's short quantum Markov chain characterization, valid also when $\rho_B$ is singular.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 4, Section V, unnumbered equation (11): local Markov recovery characterization

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

/-- PDF p.4, eq.(11), and p.5: recovery acts on B alone, with the identity on A. -/
theorem ssaEquality_iff_localRecovery {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hrho : IsDensityMatrix rho) :
    quantumCMI rho = 0 ↔ ∃ r : Superop B (B × C),
      IsChannel r ∧ idTensorSuperop (R := A) r (marginalAB rho) = rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
