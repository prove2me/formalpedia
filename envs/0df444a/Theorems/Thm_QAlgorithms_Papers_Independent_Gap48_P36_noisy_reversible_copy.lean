-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_noisy_reversible_copy
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.noisy_reversible_copy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:57:51.288568+00:00
-- url     : https://prove2.me/theorems/b9bf034a-8079-4f9d-984d-02e8649500ba
-- title:
--   Theorem 10: the noisy conjugate contains a reversible copy of every input
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $T=(T_m)$ be a basis of $d^2$ unitaries on $\mathbb C^d$, including $I$, with $\operatorname{Tr}(T_m^\dagger T_n)=d\delta_{mn}$. Write $N^{C,T}$ for the canonical conjugate using Kraus matrices $T_m/d$, and $\mathcal N^T=\{N^{C,T}(|\psi\rangle\langle\psi|):\|\psi\|=1\}$. There is one unitary $U_T:\mathbb C^d\otimes\mathbb C^d\to\mathbb C^{d^2}$, independent of the density matrix $\rho$, such that
--
--   $$
--   N^{C,T}(\rho)=U_T\bigl((I_d/d)\otimes\rho\bigr)U_T^\dagger.
--   $$
--
--   Mixed inputs are included. This displays a reversible copy of every input in the environment.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 19, Theorem 10: the noisy conjugate contains a reversible copy of every input

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

/-- Theorem 10, PDF p.19: one unitary before all density inputs, including mixed inputs.
U is rectangular only in its labeling: the two dimensions are both d^2. -/
theorem noisy_reversible_copy [Nonempty A] [Nonempty K] (T : UnitaryBasis A K) :
    ∃ U : Matrix K (A × A) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ rho : Matrix A A ℂ, IsDensityMatrix rho →
        noisyComplement T.matrix rho = U * (((Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ)) ⊗ₖ rho) * Uᴴ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
