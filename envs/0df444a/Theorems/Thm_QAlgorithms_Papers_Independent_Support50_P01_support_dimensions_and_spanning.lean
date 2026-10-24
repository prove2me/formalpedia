-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_support_dimensions_and_spanning
-- name    : QAlgorithms.Papers.Independent.Support50.P01.support_dimensions_and_spanning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:20:23.431793+00:00
-- url     : https://prove2.me/theorems/ec298c63-510b-4e60-bae6-504f0ab80323
-- title:
--   Lemma 1: support dimensions and spanning of the environment
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. Assume conjugate degradability and fix any finite family of unit vectors $\psi_1,\ldots,\psi_m$. Set $B_j=\operatorname{range}\mathcal N(\psi_j)$ and $E_j=\operatorname{range}\mathcal N^c(\psi_j)$, writing $\psi_j$ also for its rank-one projector. Then
--   $$
--   \dim B_j=\dim E_j\quad(1\le j\le m),\qquad
--   \left[e=\operatorname{rank}J(\mathcal N),\ \operatorname{span}_j B_j=B\right]
--   \Longrightarrow \operatorname{span}_j E_j=E.
--   $$
--   The minimal-environment condition is imposed only on the spanning conclusion.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 12, Lemma 1: support dimensions and spanning of the environment

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

/-- PDF pp.12–13, Lemma 1: equal support dimensions and environment spanning.
Minimality e=Choi rank is required only for the second conclusion. -/
theorem support_dimensions_and_spanning (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U)
    (m : ℕ) (psi : Fin m → EuclideanSpace ℂ (Fin a)) (hpsi : ∀ j, ‖psi j‖ = 1) :
    (∀ j, (receiverChannel U (pureDensity (psi j))).rank =
      (complementaryChannel U (pureDensity (psi j))).rank) ∧
    (e = (outputFirstChoi (receiverChannel U)).rank →
      (⨆ j, LinearMap.range (receiverChannel U (pureDensity (psi j))).mulVecLin) = ⊤ →
      (⨆ j, LinearMap.range (complementaryChannel U (pureDensity (psi j))).mulVecLin) = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
