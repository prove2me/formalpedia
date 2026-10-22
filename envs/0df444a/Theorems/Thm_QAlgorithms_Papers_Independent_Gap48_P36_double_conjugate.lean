-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_double_conjugate
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.double_conjugate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:04:44.073657+00:00
-- url     : https://prove2.me/theorems/28c1b085-067b-4db5-b7db-c422d51d3a6e
-- title:
--   Unnumbered: the original channel is a conjugate of its conjugate
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For every channel $\Phi$ and every chosen conjugate $\Phi^C$,
--
--   $$
--   \Phi\in\mathcal C(\Phi^C).
--   $$
--
--   This asserts membership in the conjugate class, not equality to an independently chosen double-conjugate representative.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 7, Unnumbered: the original channel is a conjugate of its conjugate

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

/-- Unnumbered double-conjugate assertion, PDF p.7: symmetry of the same dilation.
An independently chosen double complement need only be equivalent. -/
theorem double_conjugate [Nonempty A] [Nonempty B] [Nonempty C]
    (Phi : Superop A B) (PhiC : Superop A C) (hPhi : IsChannel Phi)
    (hc : CPComplementary Phi PhiC) : CPComplementary PhiC Phi := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
