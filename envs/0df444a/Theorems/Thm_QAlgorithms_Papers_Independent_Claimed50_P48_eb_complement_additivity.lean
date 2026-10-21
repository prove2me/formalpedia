-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_eb_complement_additivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.eb_complement_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:52:13.506208+00:00
-- url     : https://prove2.me/theorems/d0d6cb49-ab1e-4c7d-a8c6-a135a1501898
-- title:
--   Multiplicativity and entropy additivity for the full class (14)
-- statement:
--   Let $c$ be any finite positive semidefinite matrix and $\psi_\alpha$ arbitrary vectors in a nonzero finite input space. Define $T(X)_{\alpha\beta}=c_{\alpha\beta}\langle\psi_\alpha|X|\psi_\beta\rangle$. For finite real $p>1$ and every CP partner $\Psi$ with nonzero input,
--
--   $$\nu_p(T\otimes\Psi)=\nu_p(T)\nu_p(\Psi).$$
--
--   If $T$ is trace preserving, then for every channel $\Psi$,
--
--   $$\check H(T\otimes\Psi)=\check H(T)+\check H(\Psi),\qquad
--   \widehat H_{T\otimes\Psi}(\rho_{12})\ge\widehat H_T(\rho_1)+\widehat H_\Psi(\rho_2)$$
--
--   for every joint density $\rho_{12}$ and its input marginals $\rho_1,\rho_2$. These are the advertised properties of the full class (14), without requiring an orthonormal family $\psi$.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 6, Multiplicativity and entropy additivity for the full class (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF pp.5–6: the full (14) class, finite p>1 for CP maps, and under
channel normalization entropy additivity AND all-state superadditivity. -/
theorem eb_complement_additivity [Nonempty A]
    (c : Matrix K K ℂ) (hc : c.PosSemidef) (psi : K → EuclideanSpace ℂ A) :
    (∀ p : ℝ, 1 < p → UniversalMultiplicative (ENNReal.ofReal p) (arbitraryVectorComplement c psi)) ∧
    (IsChannel (arbitraryVectorComplement c psi) → UniversalAdditive (arbitraryVectorComplement c psi) ∧
      UniversalSuperadditive (arbitraryVectorComplement c psi)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
