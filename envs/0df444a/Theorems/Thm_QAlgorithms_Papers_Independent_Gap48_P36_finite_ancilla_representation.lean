-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_finite_ancilla_representation
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.finite_ancilla_representation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:10:35.83753+00:00
-- url     : https://prove2.me/theorems/eda435eb-73e3-42ae-a6d3-5dc187284b68
-- title:
--   Unnumbered appendix result (87): finite pure-ancilla representation
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. For every channel $\Phi:M_d\to M_{d_B}$ there are a positive finite ancilla dimension $r$, its first unit basis vector $e_1$, and a rectangular partial isometry $U:\mathbb C^d\otimes\mathbb C^r\to\mathbb C^{d_B}\otimes\mathbb C^r$ such that every matrix $B$ satisfies
--
--   $$
--   \Phi(B)=\operatorname{Tr}_{\mathrm{anc}}\bigl[U(B\otimes|e_1\rangle\langle e_1|)U^\dagger\bigr].
--   $$
--
--   This retains the finite pure-ancilla representation (87), without the unsupported surrounding rank prescription.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 28, Unnumbered appendix result (87): finite pure-ancilla representation

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

/-- Unnumbered finite ancilla representation (87), PDF pp.28–29.
No unsupported rank d*kappa constraint is added. -/
theorem finite_ancilla_representation [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) :
    ∃ r : ℕ, ∃ hr : 0 < r, ∃ U : Matrix (B × Fin r) (A × Fin r) ℂ,
      PartialIsometry U ∧ ∀ rho, Phi rho =
        traceRight (U * (rho ⊗ₖ pureDensity (ket (⟨0,hr⟩ : Fin r))) * Uᴴ) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
