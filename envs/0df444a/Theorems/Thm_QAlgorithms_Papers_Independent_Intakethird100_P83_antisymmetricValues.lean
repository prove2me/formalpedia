-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_antisymmetricValues
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.antisymmetricValues
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:14:59.356087+00:00
-- url     : https://prove2.me/theorems/ef4eec40-318b-439e-8122-884a0e6a497b
-- title:
--   Exact entanglement of the qutrit antisymmetric state
-- statement:
--   Let $F$ be the swap operator on $\mathbb C^3\otimes\mathbb C^3$, defined by $F|ij\rangle=|ji\rangle$, and define the normalized antisymmetric state $\sigma_3=(I-F)/6$. Then
--
--   $$E_\Gamma(\sigma_3)=E_W(\sigma_3)=E_N(\sigma_3)=\log_2(5/3).$$
--
--   Here $E_\Gamma$ is the vanishing-error PPT rate, $E_W$ is the logarithm of SDP (7), and $E_N$ is logarithmic negativity. This contrasts with the symmetric-support example in Proposition 5.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 4, Unnumbered Remark: exact entanglement of the normalized qutrit antisymmetric state

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Remark, PDF p.4: exact PPT entanglement values of the constructed
normalized qutrit antisymmetric state. -/
theorem antisymmetricValues :
    IsDensityMatrix qutritAntisymmetricState ∧
    entanglementGamma qutritAntisymmetricState = Real.logb 2 (5/3) ∧
    entanglementW qutritAntisymmetricState = Real.logb 2 (5/3) ∧
    entanglementN qutritAntisymmetricState = Real.logb 2 (5/3) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
