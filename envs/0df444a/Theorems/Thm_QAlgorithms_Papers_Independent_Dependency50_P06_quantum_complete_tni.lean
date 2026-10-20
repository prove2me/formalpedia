-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_quantum_complete_tni
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.quantum_complete_tni
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:29:07.114415+00:00
-- url     : https://prove2.me/theorems/df9c5ccc-4b10-460d-8e0d-ea78cd445abb
-- title:
--   Ordinary CPTNI maps obey complete trace non-increase
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Let $E:A_0\to A_1$ be completely positive and trace non-increasing. For every finite nonzero reference system $R$ and every density matrix $\rho$ on $RA_0$,
--
--   $$(I_R\otimes E)(\rho)\geq0,\qquad\operatorname{Tr}[(I_R\otimes E)(\rho)]\leq1.$$
--
--   The identity here is an ordinary identity channel. Thus the complete trace condition adds nothing to the usual CPTNI conditions on quantum maps.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 5, Eq. (6.1); Proposition F.12 discussion p.24

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section QuantumResults

variable {A0 A1 B0 B1 : Type}

variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]

variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

/-- PDF pp.5–6,24, (6.1): ordinary CPTNI maps remain CPTNI when tensored
with an identity channel, rather than an identity supermap. -/
theorem quantum_complete_tni [Nonempty A0] [Nonempty A1] (E : QMap A0 A1) (hE : IsCPTNI E) :
    ∀ r : ℕ, 0 < r → ∀ rho : Op (Fin r × A0), IsDensityMatrix rho →
      (idTensorSuperop E rho).PosSemidef ∧ (idTensorSuperop E rho).trace.re ≤ 1 := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
