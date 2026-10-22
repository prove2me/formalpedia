-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_hadamard_strong_additivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.hadamard_strong_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:55:47.58918+00:00
-- url     : https://prove2.me/theorems/3035f388-9f57-41b1-956a-fae729bf8a59
-- title:
--   Theorem 7: strong purity and Holevo additivity for general Hadamard channels
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. Let $\Phi_1$ have normalized Kraus operators $R_m=\sum_j c_{jm}|e_j\rangle\langle w_j|$, where the $e_j$ are an orthonormal output basis and the $w_j$ are independent of $m$. For every channel $\Phi_2$,
--
--   $$
--   \begin{gathered}\nu_p(\Phi_1\otimes\Phi_2)=\nu_p(\Phi_1)\nu_p(\Phi_2)\quad(p\ge1),\\ S_{\min}(\Phi_1\otimes\Phi_2)=S_{\min}(\Phi_1)+S_{\min}(\Phi_2),\\C_{\mathrm{Holv}}(\Phi_1\otimes\Phi_2)=C_{\mathrm{Holv}}(\Phi_1)+C_{\mathrm{Holv}}(\Phi_2).\end{gathered}
--   $$
--
--   Here $C_{\mathrm{Holv}}$ is the supremum of the single-use Holevo quantity over finite input ensembles. The $w_j$ need not be orthogonal, and the output dimension may exceed the input dimension.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 12, Theorem 7: strong purity and Holevo additivity for general Hadamard channels

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

/-- Theorem 7, PDF pp.11–13: arbitrary common-vector Kraus maps, with all three conclusions.
The partner and finite exponent are unrestricted in the source's domains. -/
theorem hadamard_strong_additivity [Nonempty A] [Nonempty B] [Nonempty K] [Nonempty A2] [Nonempty B2]
    (v : Matrix K B ℂ) (w : K → EuclideanSpace ℂ A)
    (hF : IsKrausFamily (gramKraus v w)) (Psi : Superop A2 B2) (hPsi : IsChannel Psi) :
    (∀ p : ℝ, 1 ≤ p → Multiplicative (ENNReal.ofReal p) (krausApply (gramKraus v w)) Psi) ∧
    Additive (krausApply (gramKraus v w)) Psi ∧
    holevoCapacity (superopTensor (krausApply (gramKraus v w)) Psi) =
      holevoCapacity (krausApply (gramKraus v w)) + holevoCapacity Psi := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
