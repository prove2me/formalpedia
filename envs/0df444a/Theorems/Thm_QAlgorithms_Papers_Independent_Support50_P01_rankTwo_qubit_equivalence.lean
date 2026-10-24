-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_rankTwo_qubit_equivalence
-- name    : QAlgorithms.Papers.Independent.Support50.P01.rankTwo_qubit_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:24:13.988243+00:00
-- url     : https://prove2.me/theorems/9206d752-24c1-4080-b712-20100e9efa77
-- title:
--   Theorem 6(i): rank-two qubit EB/conjugate-antidegradable equivalence
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. Suppose $a=b=2$ and $\operatorname{rank}J(\mathcal N)=2$. Then
--   $$\mathcal N\text{ is entanglement breaking}\quad\Longleftrightarrow\quad
--   \mathcal N\text{ is conjugate antidegradable}.$$
--   Singular channels are included; the inverse-channel expressions in the proof are not additional hypotheses. The separate printed mutual-exclusion claim is not asserted.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 14, Theorem 6(i): rank-two qubit EB/conjugate-antidegradable equivalence

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

/-- PDF pp.14–15, Theorem 6(i): no inverse-channel hypothesis is imposed.
Part (ii) is separately deferred because complete dephasing refutes it. -/
theorem rankTwo_qubit_equivalence {e : ℕ} (he : 0<e)
    (U : Matrix (Fin 2 × Fin e) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (hrank : (outputFirstChoi (receiverChannel U)).rank = 2) :
    EntanglementBreaking (by decide) (by decide) (receiverChannel U) ↔ ConjugateAntidegradable U := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
