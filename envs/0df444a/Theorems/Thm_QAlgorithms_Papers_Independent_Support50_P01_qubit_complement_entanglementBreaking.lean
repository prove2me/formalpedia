-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_qubit_complement_entanglementBreaking
-- name    : QAlgorithms.Papers.Independent.Support50.P01.qubit_complement_entanglementBreaking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:10:46.780423+00:00
-- url     : https://prove2.me/theorems/ba888a89-d6e4-492c-9a5c-3d2e883b61b7
-- title:
--   §II.C: conjugate degradable qubit channels have EB complements
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. If $a=b=2$ and $\mathcal N$ is conjugate degradable, then
--   $$\mathcal N^c\ \text{is entanglement breaking},\qquad \mathcal N\ \text{is ordinarily degradable}.$$
--   The Choi-rank bound is not an added hypothesis, and the conclusion is invariant under padding the chosen environment.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 5, §II.C: conjugate degradable qubit channels have EB complements

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

/-- PDF p.5: qubit-to-qubit conjugate degradable channels have EB complements.
No Choi-rank bound is assumed in place of the source's conclusion. -/
theorem qubit_complement_entanglementBreaking {e : ℕ} (he : 0<e)
    (U : Matrix (Fin 2 × Fin e) (Fin 2) ℂ) (hU : ConjugateDegradable U) :
    EntanglementBreaking (by decide) he (complementaryChannel U) ∧ IsDegradable U := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
