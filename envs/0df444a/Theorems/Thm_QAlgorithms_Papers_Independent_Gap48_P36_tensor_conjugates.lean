-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_tensor_conjugates
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.tensor_conjugates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:05:26.05213+00:00
-- url     : https://prove2.me/theorems/a62f4856-da64-4ebf-acec-703ba1813897
-- title:
--   Unnumbered tensor conjugacy and partial-isometry relation (15)
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For conjugate pairs $\Phi_i,\Phi_i^C$ one has
--
--   $$
--   \Phi_1^C\otimes\Phi_2^C\in\mathcal C(\Phi_1\otimes\Phi_2).
--   $$
--
--   For every other conjugate $\Xi$ of the product, there is a fixed rectangular partial isometry $W$ such that $\Xi(\rho)=W(\Phi_1^C\otimes\Phi_2^C)(\rho)W^\dagger$ for all joint matrices $\rho$, including entangled inputs.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 8, Unnumbered tensor conjugacy and partial-isometry relation (15)

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

/-- Unnumbered tensor conjugacy and (15), PDF p.8: all entangled joint inputs are included. -/
theorem tensor_conjugates [Nonempty A] [Nonempty B] [Nonempty C]
    [Nonempty A2] [Nonempty B2] [Nonempty C2] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop A2 B2)
    (PhiC : Superop A C) (PsiC : Superop A2 C2)
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi)
    (hc : CPComplementary Phi PhiC) (hd : CPComplementary Psi PsiC) :
    CPComplementary (superopTensor Phi Psi) (superopTensor PhiC PsiC) ∧
    ∀ Xi : Superop (A × A2) D, CPComplementary (superopTensor Phi Psi) Xi →
      ∃ W : Matrix D (C × C2) ℂ, PartialIsometry W ∧
        ∀ rho, Xi rho = W * superopTensor PhiC PsiC rho * Wᴴ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
