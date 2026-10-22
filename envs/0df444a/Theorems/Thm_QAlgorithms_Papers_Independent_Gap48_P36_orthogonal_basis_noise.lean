-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_orthogonal_basis_noise
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.orthogonal_basis_noise
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:13:30.241538+00:00
-- url     : https://prove2.me/theorems/5a8e2dd3-2b5a-4800-b830-931fe03e805b
-- title:
--   Unnumbered (31): a unitary orthogonal basis gives the completely noisy channel
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $T=(T_m)$ be a basis of $d^2$ unitaries on $\mathbb C^d$, including $I$, with $\operatorname{Tr}(T_m^\dagger T_n)=d\delta_{mn}$. For every complex input matrix $\rho$,
--
--   $$
--   \frac1{d^2}\sum_m T_m\rho T_m^\dagger=\frac{\operatorname{Tr}\rho}{d}I_d.
--   $$
--
--   Thus each such basis generates the completely noisy channel. The identity includes nonstates and the case $d=1$.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 14, Unnumbered (31): a unitary orthogonal basis gives the completely noisy channel

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

/-- Unnumbered twirling identity (31), PDF p.14: every input matrix, including nonstates. -/
theorem orthogonal_basis_noise [Nonempty A] [Nonempty K] (T : UnitaryBasis A K) :
    ∀ rho : Matrix A A ℂ,
      ((Fintype.card A : ℂ)^2)⁻¹ • (∑ k, T.matrix k * rho * (T.matrix k)ᴴ) =
        (rho.trace / (Fintype.card A : ℂ)) • (1 : Matrix A A ℂ) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
