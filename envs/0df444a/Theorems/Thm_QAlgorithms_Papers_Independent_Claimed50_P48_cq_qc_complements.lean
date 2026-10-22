-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_cq_qc_complements
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.cq_qc_complements
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:44:40.568071+00:00
-- url     : https://prove2.me/theorems/7cc9c71c-35ae-4205-b6dc-fe30a0f3a85b
-- title:
--   Classical–quantum and quantum–classical special cases
-- statement:
--   Let $U$ be an orthonormal input basis matrix and let $\varphi_\alpha$ be arbitrary output vectors. The rank-one pure-preparation c-q map, with input vectors $\psi_\alpha=Ue_\alpha$, has complementary map
--
--   $$T(X)=c\mathbin{\circ}(U^*XU),\qquad c_{\alpha\beta}=\langle\varphi_\beta|\varphi_\alpha\rangle.$$
--
--   Here $\circ$ denotes entrywise multiplication. It is a channel exactly when every $c_{\alpha\alpha}=1$. Conversely, for arbitrary input vectors $\psi_\alpha$ and an orthonormal output basis $\varphi_\alpha=We_\alpha$, the Gram matrix is $I$, the original map is $WT_{I,\psi}(X)W^*$, and its complement is $T_{I,\psi}$. Thus both are the same diagonal measurement map after output-basis identification. This states the source's special c-q and q-c cases without allowing mixed preparations in the c-q subclass.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 5, Classical–quantum and quantum–classical special cases

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

/-- PDF p.5: c-q is the pure-preparation subclass; q-c is the same diagonal
measurement map after identifying the two output bases. -/
theorem cq_qc_complements [Nonempty A]
    (U : Matrix.unitaryGroup A ℂ) (phi : A → EuclideanSpace ℂ B) :
    (∀ rho, arbitraryVectorComplement (gram phi) (basisColumns U) rho =
      Matrix.hadamard (gram phi) ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) ∧
    CPComplementary (krausApply (rankOneKraus (basisColumns U) phi)) (arbitraryVectorComplement (gram phi) (basisColumns U)) ∧
    (IsChannel (arbitraryVectorComplement (gram phi) (basisColumns U)) ↔ ∀ a, gram phi a a = 1) ∧
    (∀ (psi : B → EuclideanSpace ℂ A) (W : Matrix.unitaryGroup B ℂ),
      gram (basisColumns W) = 1 ∧
      (∀ rho, krausApply (rankOneKraus psi (basisColumns W)) rho =
        (W : Matrix B B ℂ) * arbitraryVectorComplement 1 psi rho * (W : Matrix B B ℂ)ᴴ) ∧
      CPComplementary (krausApply (rankOneKraus psi (basisColumns W))) (arbitraryVectorComplement 1 psi)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
