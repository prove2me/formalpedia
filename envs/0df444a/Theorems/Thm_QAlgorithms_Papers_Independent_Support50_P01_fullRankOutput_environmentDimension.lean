-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_fullRankOutput_environmentDimension
-- name    : QAlgorithms.Papers.Independent.Support50.P01.fullRankOutput_environmentDimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:21:24.345884+00:00
-- url     : https://prove2.me/theorems/6a2be427-8237-4402-b270-b108d01bcbbc
-- title:
--   Theorem 3: full-rank pure output and environment dimension
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. Assume conjugate degradability and a minimal environment, $e=\operatorname{rank}J(\mathcal N)$. If some unit vector $\psi$ satisfies $\operatorname{rank}\mathcal N(|\psi\rangle\langle\psi|)=b$, then
--   $$b=e.$$
--   This identifies the minimal environment dimension from a full-rank output of a pure input.
--
--   **Formalization Note** The printed extra application $\operatorname{rank}\mathcal N(\rho)$, after defining $\rho=\mathcal N(\psi)$, is corrected to $\operatorname{rank}\rho$, as used in the source proof.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 13, Theorem 3: full-rank pure output and environment dimension

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

/-- PDF p.13, Theorem 3: the printed rank N(rho), after rho=N(psi), is ill-typed
for rectangular channels. The proof uses rank rho=dim B, which is stated here.
A minimal environment is required; arbitrary isometric padding would refute the claim. -/
theorem fullRankOutput_environmentDimension (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U)
    (hminimal : e = (outputFirstChoi (receiverChannel U)).rank)
    (hfull : ∃ psi : EuclideanSpace ℂ (Fin a), ‖psi‖ = 1 ∧
      (receiverChannel U (pureDensity psi)).rank = b) : b=e := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
