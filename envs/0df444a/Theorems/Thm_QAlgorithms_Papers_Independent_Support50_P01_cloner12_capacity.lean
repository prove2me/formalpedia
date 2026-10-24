-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloner12_capacity
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloner12_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:11:46.667176+00:00
-- url     : https://prove2.me/theorems/ac8ac0a4-e100-4cee-b2c5-d02cdf83d2ca
-- title:
--   §III.A, Eq.(10): capacity and optimizer of the 1→2 cloner
-- statement:
--   Let $1\le N\le M$ be integers. Let $\mathrm{Cl}_{N,M}$ be the specified optimal universal qubit cloner on $\operatorname{Sym}^N(\mathbb C^2)$, with receiver support $\operatorname{Sym}^M(\mathbb C^2)$ and environment dimension $M-N+1$. Its common dilation on normalized occupation kets is exactly Eqs.(21),(22). Write $\pi_d=I_d/d$, $I_c$ for coherent information in bits, $Q^{(1)}$ for its supremum over all density inputs, and $Q$ for its regularization over all positive block lengths and arbitrary entangled block inputs. For the $1\to2$ case,
--   $$
--   \mathrm{Cl}_{1,2}(\pi_2)=\pi_3,\quad \mathrm{Cl}_{1,2}^c(\pi_2)=\pi_2,\quad
--   I_c(\mathrm{Cl}_{1,2},\rho)\le I_c(\mathrm{Cl}_{1,2},\pi_2)=Q^{(1)}(\mathrm{Cl}_{1,2}),\quad
--   Q(\mathrm{Cl}_{1,2})=\log_2 3-1.
--   $$
--   The inequality holds for every density input $\rho$. The receiver identity is on the three-dimensional symmetric support, equivalent to $\Pi_+/3$ on two qubits.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 6, §III.A, Eq.(10): capacity and optimizer of the 1→2 cloner

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

/-- PDF pp.5–6, Eq.(10): capacity, optimizer and both normalized maximally mixed outputs. -/
theorem cloner12_capacity :
    quantumCapacity (receiverChannel (clonerDilation 1 2)) = Real.logb 2 3 - 1 ∧
    receiverChannel (clonerDilation 1 2) (maximallyMixed 2) = maximallyMixed 3 ∧
    complementaryChannel (clonerDilation 1 2) (maximallyMixed 2) = maximallyMixed 2 ∧
    IsDensityMatrix (maximallyMixed 2) ∧
    coherentInformation (receiverChannel (clonerDilation 1 2)) (maximallyMixed 2) =
      maximumCoherentInformation (clonerDilation 1 2) ∧
    ∀ rho, IsDensityMatrix rho → coherentInformation (receiverChannel (clonerDilation 1 2)) rho ≤
      coherentInformation (receiverChannel (clonerDilation 1 2)) (maximallyMixed 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
