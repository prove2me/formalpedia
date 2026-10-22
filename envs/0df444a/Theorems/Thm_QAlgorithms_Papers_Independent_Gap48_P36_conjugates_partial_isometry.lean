-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_conjugates_partial_isometry
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.conjugates_partial_isometry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:51:48.63023+00:00
-- url     : https://prove2.me/theorems/75c999c9-ef2e-4c21-bf90-e8da76e39420
-- title:
--   Lemma 1: conjugates are equivalent by a rank-kappa partial isometry
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Let $\Psi,\Xi$ be two conjugates of a channel $\Phi$, whose minimum Kraus number is $\kappa$. There is a rectangular matrix $W$ with $WW^\dagger W=W$ and rank $\kappa$ such that every matrix $\rho$ obeys
--
--   $$
--   \Psi(\rho)=W\Xi(\rho)W^\dagger,\qquad\Xi(\rho)=W^\dagger\Psi(\rho)W.
--   $$
--
--   This includes nonminimal environments and both directions of equivalence.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 6, Lemma 1: conjugates are equivalent by a rank-kappa partial isometry

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

/-- Lemma 1, PDF pp.6–7: both all-operator identities and the minimal Kraus rank. -/
theorem conjugates_partial_isometry [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop A C) (Xi : Superop A D)
    (hPhi : IsChannel Phi) (hPsi : CPComplementary Phi Psi) (hXi : CPComplementary Phi Xi) :
    ∃ W : Matrix C D ℂ, PartialIsometry W ∧ Matrix.rank W = krausNumber Phi ∧
      (∀ rho, Psi rho = W * Xi rho * Wᴴ) ∧ (∀ rho, Xi rho = Wᴴ * Psi rho * W) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
