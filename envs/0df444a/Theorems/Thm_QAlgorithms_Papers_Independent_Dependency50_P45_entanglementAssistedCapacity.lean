-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_entanglementAssistedCapacity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.entanglementAssistedCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:00:56.434988+00:00
-- url     : https://prove2.me/theorems/c1588057-4b2e-4887-8ac4-9b1db123eab2
-- title:
--   Theorem 1: entanglement-assisted classical capacity
-- statement:
--   Let $\mathcal N$ be a memoryless CPTP map between nonzero finite-dimensional complex Hilbert spaces. Let $C_E(\mathcal N)$ be its operational classical capacity with unlimited message-independent prior EPR pairs, arbitrary local CPTP encoders, collective decoding, and no other communication. Every message must be recovered with uniformly vanishing error; inputs across channel uses may be entangled. For a density matrix $\rho$, let $\Phi_\rho$ be a normalized purification and let $H$ denote von Neumann entropy in bits, with $0\log 0=0$. Then the maximum is attained and
--
--   $$C_E(\mathcal N)=\max_{\rho\ge0,\ \operatorname{Tr}\rho=1}\bigl[H(\rho)+H(\mathcal N(\rho))-H((\operatorname{id}\otimes\mathcal N)\Phi_\rho)\bigr].$$
--
--   This identifies an operational communication rate with a single-use entropy optimization. The reference factor is written first in the formalization.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 8, Theorem 1: entanglement-assisted classical capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF pp.8--9, Theorem 1, Eqs.(7),(9): operational capacity equals an attained maximum. -/
theorem entanglementAssistedCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) :
    IsGreatest {v | ∃ rho : Matrix A A ℂ,
      IsDensityMatrix rho ∧ v = inputMutualInfo N rho} (resourceCapacity standardEbit N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
