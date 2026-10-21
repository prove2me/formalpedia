-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_separable_iff_ssaExtension
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.separable_iff_ssaExtension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:02:33.659106+00:00
-- url     : https://prove2.me/theorems/e079a806-ae4f-4955-9ad7-18e7f642506c
-- title:
--   Corollary 7: separable marginal iff an SSA-equality extension exists
-- statement:
--   Let $A,C$ be nonzero finite-dimensional complex spaces. Every tripartite density $\rho_{ABC}$ with zero conditional mutual information has a separable marginal $\rho_{AC}$. Conversely, for each density $\sigma_{AC}$,
--
--   $$\sigma_{AC}\text{ is separable}\quad\Longleftrightarrow\quad\exists B,\rho_{ABC}:\ \operatorname{Tr}_B\rho_{ABC}=\sigma_{AC},\quad I(A:C\mid B)_\rho=0.$$
--
--   Here $B$ is some nonzero finite-dimensional space chosen after $\sigma_{AC}$; separability means a finite convex combination of tensor products of normalized densities. All conditional mutual informations are the four-entropy expression in bits. This identifies precisely the marginals admitting an SSA-equality extension.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 5, Corollary 7: separable marginal iff an SSA-equality extension exists

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

/-- PDF p.5, Corollary 7: both directions; the extension register is chosen after the marginal. -/
theorem separable_iff_ssaExtension {A C : Type}
    [Fintype A] [Fintype C] [Nonempty A] [Nonempty C]
    (s : Matrix (A × C) (A × C) ℂ) (hs : IsDensityMatrix s) :
    (∀ b : ℕ, ∀ rho : Matrix (A × (Fin b × C)) (A × (Fin b × C)) ℂ,
      IsDensityMatrix rho → quantumCMI rho = 0 →
        Entanglement.IsSeparableDensity (marginalAC rho)) ∧
    (Entanglement.IsSeparableDensity s ↔ ∃ b : ℕ, 0 < b ∧
      ∃ rho : Matrix (A × (Fin b × C)) (A × (Fin b × C)) ℂ,
        IsDensityMatrix rho ∧ marginalAC rho = s ∧ quantumCMI rho = 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
