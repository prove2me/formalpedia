-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_conjugate_kraus_reshuffling
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.conjugate_kraus_reshuffling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:03:59.135935+00:00
-- url     : https://prove2.me/theorems/4999d915-ef6e-48a9-af1a-e2d4f5da9b0c
-- title:
--   Unnumbered construction (6)–(8): conjugate Kraus reshuffling
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For normalized Kraus matrices $F_j:\mathcal H_A\to\mathcal H_B$, let $V_{(b,j),a}=(F_j)_{ba}$ and $(R_b)_{ja}=(F_j)_{ba}$. The complement of this fixed dilation satisfies, for every matrix $\rho$,
--
--   $$
--   \Phi^C(\rho)_{jk}=\operatorname{Tr}(F_j\rho F_k^\dagger),\qquad\Phi^C(\rho)=\sum_b R_b\rho R_b^\dagger.
--   $$
--
--   The reshuffled operators are determined independently of the input.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 5, Unnumbered construction (6)–(8): conjugate Kraus reshuffling

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

/-- Unnumbered construction (7)–(8), PDF pp.5–6: reshuffling is independent of rho. -/
theorem conjugate_kraus_reshuffling [Nonempty A] [Nonempty B] [Nonempty K]
    (F : K → Matrix B A ℂ) (hF : IsKrausFamily F) :
    (∀ b j a, rowKraus F b j a = F j b a) ∧
    complementaryChannel (indexedKrausDilation F) = krausApply (rowKraus F) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
