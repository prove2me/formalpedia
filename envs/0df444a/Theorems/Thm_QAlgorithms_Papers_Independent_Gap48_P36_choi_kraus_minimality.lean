-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_choi_kraus_minimality
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.choi_kraus_minimality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:11:18.79028+00:00
-- url     : https://prove2.me/theorems/4f646a95-fb3d-42c8-9fe5-d2239b5c7aa8
-- title:
--   Unnumbered appendix result: Choi rank equals minimum Kraus number
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For $\Phi:M_d\to M_{d_B}$ let $\Gamma=d^{-1}\sum_{j,k}|j\rangle\langle k|\otimes\Phi(|j\rangle\langle k|)$. Choose its orthonormal spectral basis, retain nonzero eigenvalues $\lambda_\mu$ with multiplicities, and reshape $G_\mu(b,a)=\sqrt{d\lambda_\mu}\,z_\mu(a,b)$. Then
--
--   $$
--   \operatorname{rank}\Gamma=\kappa=\min\{\text{number of Kraus operators for }\Phi\}\le d\,d_B.
--   $$
--
--   The computed family $G_\mu$ is normalized, represents $\Phi$, and has exactly $\kappa$ members. Tensor pair indices avoid the faulty flattening factor.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 30, Unnumbered appendix result: Choi rank equals minimum Kraus number

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Unnumbered Choi/Kraus minimality, PDF pp.29–30: normalized Choi rank,
actual minimum Kraus number, and its dimension bound. Pair indices avoid the
printed flattening subscript (dprime-1)m+j. Correction: use the pair
(input j, output m); (88)-(89) determine this order and sqrt(d lambda). -/
theorem choi_kraus_minimality [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) :
    (normalizedChoi Phi).IsHermitian ∧
    Matrix.rank (normalizedChoi Phi) = krausNumber Phi ∧
    Fintype.card (ChoiSupport Phi) = krausNumber Phi ∧
    IsKrausFamily (spectralKraus Phi) ∧ krausApply (spectralKraus Phi) = Phi ∧
    krausNumber Phi ≤ Fintype.card A * Fintype.card B ∧
    ∃ F : Fin (krausNumber Phi) → Matrix B A ℂ, IsKrausFamily F ∧ Phi = krausApply F := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
