-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_transpose_complement_kraus_covariance
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.transpose_complement_kraus_covariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:54:43.102042+00:00
-- url     : https://prove2.me/theorems/ddc8a3a9-5c4a-4e5c-aa62-6edaae63d73f
-- title:
--   Transpose-depolarizing pair: Kraus operators and covariance
-- statement:
--   For $d\ge2$, the antisymmetric complementary channel $\Psi_d(X)=(I-F)(X\otimes I)(I-F)/[2(d-1)]$ has exactly the displayed family of $d$ Kraus maps into $\mathbb C^d\otimes\mathbb C^d$:
--
--   $$L_j\psi=\frac{\psi\otimes e_j-e_j\otimes\psi}{\sqrt{2(d-1)}},\qquad
--   \Psi_d(X)=\sum_{j=1}^{d}L_jXL_j^*.$$
--
--   For every unitary $U$ and every input operator $X$,
--
--   $$\Psi_d(UXU^*)=(U\otimes U)\Psi_d(X)(U\otimes U)^*.$$
--
--   The two tensor factors use $U$ in this example. These identities specify both the Kraus construction and covariance on arbitrary operators.
--
--   The receiver also satisfies, for every unitary $U$ and every operator $X$,
--
--   $$\Phi_d(UXU^*)=\overline U\Phi_d(X)\overline U^*,$$
--
--   where $\Phi_d(X)=(\operatorname{Tr}(X)I-X^T)/(d-1)$. This retains the page-7 receiver covariance together with the page-8 complement covariance.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 7, Transpose-depolarizing pair: Kraus operators and covariance

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

/-- PDF pp.7–8: d Kraus maps into d^2 dimensions, all-operator equality,
receiver covariance with conjugate U, and complement covariance with U tensor U. -/
theorem transpose_complement_kraus_covariance (d : ℕ) (hd : 2 ≤ d) :
    antisymmetricComplement d = krausApply (antisymmetricRows d) ∧
    (∀ (j : Fin d) (psi : EuclideanSpace ℂ (Fin d)) (ab : Fin d × Fin d),
      Matrix.mulVec (antisymmetricRows d j) (fun i => psi i) ab =
        ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) *
          (psi ab.1 * (ket j) ab.2 - (ket j) ab.1 * psi ab.2)) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      antisymmetricComplement d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) *
          antisymmetricComplement d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      wernerHolevo d ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        (U : Matrix (Fin d) (Fin d) ℂ).map conj * wernerHolevo d rho *
          ((U : Matrix (Fin d) (Fin d) ℂ).map conj)ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
