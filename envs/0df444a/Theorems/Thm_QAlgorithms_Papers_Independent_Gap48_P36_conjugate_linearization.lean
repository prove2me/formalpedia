-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_conjugate_linearization
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.conjugate_linearization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:02:31.815139+00:00
-- url     : https://prove2.me/theorems/f3ec56aa-a505-44b4-8348-80a2e6ab3d19
-- title:
--   Theorem 17: conjugate-channel linearization identities
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Fix a normalized Kraus family $F_k$, defining $\Phi(\rho)=\sum_kF_k\rho F_k^\dagger$, and an integer $p\ge1$, and set $(R_b)_{ka}=(F_k)_{ba}$. Define $\Theta(F,p)=\sum_{k_1,\ldots,k_p}\bigotimes_t F_{k_t}^\dagger F_{k_{t+1}}$ with cyclic indices. Let $L_p|a_1,\ldots,a_p\rangle=|a_2,\ldots,a_p,a_1\rangle$, and $\Omega(\Phi,p)=\widehat\Phi^{\otimes p}(L_p)$ with the computed Hilbert–Schmidt adjoint. Then
--
--   $$
--   \Omega(\Phi,p)=\Theta(\Phi^C,p)^\dagger=\Theta(\Phi,p)L_p.
--   $$
--
--   These are operator identities on the full input tensor power; the adjoint is retained.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 27, Theorem 17: conjugate-channel linearization identities

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

/-- Theorem 17, PDF pp.26–27, (79): retain the adjoint of the conjugate linearizer.
The cyclic convention is fixed by L_p|k1,...,kp>=|k2,...,kp,k1>. -/
theorem conjugate_linearization [Nonempty A] [Nonempty B] [Nonempty K]
    (F : K → Matrix B A ℂ) (hF : IsKrausFamily F) (p : ℕ) (hp : 1 ≤ p) :
    channelLinearizer (krausApply F) p = (krausLinearizer (rowKraus F) p)ᴴ ∧
    channelLinearizer (krausApply F) p = krausLinearizer F p * leftCycle A p := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
