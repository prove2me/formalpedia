-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_purified_choi_conjugate
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.purified_choi_conjugate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:52:33.524179+00:00
-- url     : https://prove2.me/theorems/e8de969d-2ad4-4a9c-9ac1-cff83c133bbd
-- title:
--   Proposition 2: purification of a normalized CJ state gives a conjugate CJ state
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For $\Phi:M_d\to M_{d_B}$ let $\Gamma_{AB}=d^{-1}\sum_{j,k}|j\rangle\langle k|\otimes\Phi(|j\rangle\langle k|)$. If the pure density $\Gamma_{ABC}$ of a unit vector purifies $\Gamma_{AB}$, there is a conjugate $\Phi^C:M_d\to M_{d_C}$ whose normalized Choi matrix satisfies
--
--   $$
--   \Gamma_{\Phi^C}=\operatorname{Tr}_B\Gamma_{ABC}.
--   $$
--
--   The purification determines the representative; the reference is the first tensor factor.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 7, Proposition 2: purification of a normalized CJ state gives a conjugate CJ state

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

/-- Proposition 2, PDF p.7 and (88), pp.29–30: the purification fixes the conjugate.
The normalized reference-first Choi matrix includes 1/d. The appendix's Tr_A
TP label on p.29 is read as Tr_B, as correctly written on p.7. -/
theorem purified_choi_conjugate [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (hPhi : IsChannel Phi)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : IsState psi)
    (hpur : traceRight (pureDensity psi) = normalizedChoi Phi) :
    ∃ PhiC : Superop A C, CPComplementary Phi PhiC ∧
      normalizedChoi PhiC = (fun ac ad => ∑ b, pureDensity psi ((ac.1,b),ac.2) ((ad.1,b),ad.2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
