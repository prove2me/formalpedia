-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_conjugateDegradable_capacity
-- name    : QAlgorithms.Papers.Independent.Support50.P01.conjugateDegradable_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:06:57.248345+00:00
-- url     : https://prove2.me/theorems/3b4e5a07-1ecb-4e57-bd8c-cc653ee4e13f
-- title:
--   §II.C, Eq.(4): single-letter capacity of conjugate degradable channels
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. If $\mathcal N$ is conjugate degradable, then
--   $$
--   Q(\mathcal N)=Q^{(1)}(\mathcal N)=I_c(\mathcal N,\rho_*),\qquad
--   I_c(\mathcal N,\rho)\le I_c(\mathcal N,\rho_*)\quad\text{for every density }\rho,
--   $$
--   for some density operator $\rho_*$. This is the attained single-letter capacity formula.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 4, §II.C, Eq.(4): single-letter capacity of conjugate degradable channels

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

/-- PDF pp.1,3–4, Eq.(4): single-letter capacity, including attainment. -/
theorem conjugateDegradable_capacity (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U) :
    quantumCapacity (receiverChannel U) = maximumCoherentInformation U ∧
    ∃ rho, IsDensityMatrix rho ∧ coherentInformation (receiverChannel U) rho = maximumCoherentInformation U ∧
      ∀ sigma, IsDensityMatrix sigma → coherentInformation (receiverChannel U) sigma ≤ coherentInformation (receiverChannel U) rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
