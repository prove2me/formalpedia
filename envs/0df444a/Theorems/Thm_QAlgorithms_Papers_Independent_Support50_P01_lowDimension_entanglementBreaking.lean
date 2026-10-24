-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_lowDimension_entanglementBreaking
-- name    : QAlgorithms.Papers.Independent.Support50.P01.lowDimension_entanglementBreaking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:10:01.426202+00:00
-- url     : https://prove2.me/theorems/fdf25a2c-cc5d-42d9-86e9-cbca8997ba96
-- title:
--   §II.C: small conjugate antidegradable channels are EB
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. If $\mathcal N$ is conjugate antidegradable and $ab\le6$, then
--   $$\mathcal N\ \text{is entanglement breaking}.$$
--   The bound concerns channel input and output dimensions. The conclusion quantifies over all finite references.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 5, §II.C: small conjugate antidegradable channels are EB

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

/-- PDF p.5: the dimension bound concerns the input and output, not arbitrary references. -/
theorem lowDimension_entanglementBreaking (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateAntidegradable U)
    (hdim : a*b ≤ 6) : EntanglementBreaking ha hb (receiverChannel U) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
