-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_complement_ppt
-- name    : QAlgorithms.Papers.Independent.Support50.P01.complement_ppt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:09:19.582555+00:00
-- url     : https://prove2.me/theorems/34a9b8d5-8d37-4d4f-bf15-6a503ea8d8c5
-- title:
--   §II.C: PPT complement and the EB special case
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. If $\mathcal N$ is conjugate degradable, then for every positive finite-dimensional reference $R$ and density operator $\rho_{RA}$,
--   $$
--   \big[(\operatorname{id}_R\otimes\mathcal N^c)(\rho_{RA})\big]^{T_E}\succeq0.
--   $$
--   Furthermore, if $\mathcal N^c$ is entanglement breaking, then $\mathcal N$ is ordinarily degradable: one CPTP map $D$ satisfies $D\mathcal N=\mathcal N^c$. Entanglement breaking means that every reference-assisted density output is separable; it is not inferred from one separable output.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 5, §II.C: PPT complement and the EB special case

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

/-- PDF p.5: PPT complement for every reference; the EB special case implies ordinary degradability. -/
theorem complement_ppt (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U) :
    (∀ r : ℕ, 0<r → ∀ X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ,
      IsDensityMatrix X → (partialTransposeOutput (idTensorSuperop (complementaryChannel U) X)).PosSemidef) ∧
    (EntanglementBreaking ha he (complementaryChannel U) → IsDegradable U) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
