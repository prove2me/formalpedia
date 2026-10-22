-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_ebt_hadamard_construction
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.ebt_hadamard_construction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:06:06.177564+00:00
-- url     : https://prove2.me/theorems/3155e63b-2a8a-429d-9aad-6e9fb45fc737
-- title:
--   Unnumbered (22)–(25): EBT conjugates and common-vector Kraus maps
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For normalized rank-one Kraus matrices $F_j=|x_j\rangle\langle w_j|$, put $X_{jk}=\langle x_k|x_j\rangle$ and $(W_\rho)_{jk}=\langle w_j|\rho|w_k\rangle$. Then the canonical conjugate is
--
--   $$
--   \Phi^C(\rho)=X\mathbin{*}W_\rho.
--   $$
--
--   Here $*$ is entrywise multiplication. Every factor $CC^\dagger=X$ gives Kraus operators $R_m=\sum_jc_{jm}|e_j\rangle\langle w_j|$ for this map. Conversely every normalized common-vector family of this form has a rank-one-Kraus, hence entanglement-breaking, conjugate. The corrected Gram order follows from tracing (23); $w_j$ need not be orthogonal.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 11, Unnumbered (22)–(25): EBT conjugates and common-vector Kraus maps

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

/-- Unnumbered (22)–(25), PDF pp.11–12: common-vector Kraus characterization.
Correction: the printed Gram <x_j|x_k> is replaced by <x_k|x_j>, forced
by tracing |x_j><x_k| in (23). The converse is included. -/
theorem ebt_hadamard_construction [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty K]
    (w : K → EuclideanSpace ℂ A) (x : K → EuclideanSpace ℂ B)
    (hF : IsKrausFamily (rankOneKraus w x)) :
    complementaryChannel (indexedKrausDilation (rankOneKraus w x)) =
      arbitraryVectorComplement (gram x) w ∧
    (∀ v : Matrix K C ℂ, v * vᴴ = gram x →
      krausApply (gramKraus v w) = arbitraryVectorComplement (gram x) w) ∧
    (∀ v : Matrix K C ℂ, IsKrausFamily (gramKraus v w) →
      HasRankOneKraus (complementaryChannel (indexedKrausDilation (gramKraus v w)))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
