-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_qubitOutput_dimensionBounds
-- name    : QAlgorithms.Papers.Independent.Support50.P01.qubitOutput_dimensionBounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:22:13.310345+00:00
-- url     : https://prove2.me/theorems/59307052-3ae0-4d7f-8c91-22e83479224a
-- title:
--   Theorem 4: input and Choi-rank bounds with qubit output
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. If $b=2$ and the channel is conjugate degradable, then
--   $$\operatorname{rank}J(\mathcal N)\le2,\qquad a\le3.$$
--   The input dimension is not assumed to be two, and no bound is placed on an artificially padded environment.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 13, Theorem 4: input and Choi-rank bounds with qubit output

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF p.13, Theorem 4: both Choi-rank and input-dimension bounds; input need not be a qubit. -/
theorem qubitOutput_dimensionBounds {e : ℕ} (ha : 0<a) (he : 0<e)
    (U : Matrix (Fin 2 × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U) :
    (outputFirstChoi (receiverChannel U)).rank ≤ 2 ∧ a≤3 := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
