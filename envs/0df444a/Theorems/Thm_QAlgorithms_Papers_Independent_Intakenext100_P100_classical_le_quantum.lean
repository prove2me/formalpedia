-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_classical_le_quantum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.classical_le_quantum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:26:17.651993+00:00
-- url     : https://prove2.me/theorems/04389658-dc2e-4883-acac-077298a896c3
-- title:
--   Measured correlation is at most quantum mutual information
-- statement:
--   Let $\rho$ be a density matrix on arbitrary positive finite local dimensions. Let $I_c(\rho)$ be the supremum of Shannon mutual information over all independent finite local POVMs and let $I_q(\rho)=S(\rho_A)+S(\rho_B)-S(\rho)$, with all entropies in bits. Then
--   $$I_c(\rho)\le I_q(\rho).$$
--   This is the independently useful endpoint inequality established in Eq. (23); no relative-entropy identity or optimizing POVM is assumed as a hypothesis.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 6, Eq. (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Eq.(23): independent locally measured classical correlation is
at most quantum mutual information, for arbitrary finite positive dimensions. -/
theorem classical_le_quantum {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    lockingMeasuredInformation rho ≤ Support50.P39.quantumMutualInformation rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
