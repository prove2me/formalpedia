-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloningFamilies_conjugateDegradable
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloningFamilies_conjugateDegradable
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:15:11.575695+00:00
-- url     : https://prove2.me/theorems/11b33756-66fd-402f-af1e-5b7b7aceacc8
-- title:
--   Theorem 1: conjugate degradability of two cloning families
-- statement:
--   Let $1\le N\le M$ be integers. Let $\mathrm{Cl}_{N,M}$ be the specified optimal universal qubit cloner on $\operatorname{Sym}^N(\mathbb C^2)$, with receiver support $\operatorname{Sym}^M(\mathbb C^2)$ and environment dimension $M-N+1$. Its common dilation on normalized occupation kets is exactly Eqs.(21),(22). Write $\pi_d=I_d/d$, $I_c$ for coherent information in bits, $Q^{(1)}$ for its supremum over all density inputs, and $Q$ for its regularization over all positive block lengths and arbitrary entangled block inputs. The two families satisfy
--   $$
--   \mathrm{Cl}_{N,N+1}\text{ is conjugate degradable}\quad(N\ge1),\qquad
--   \mathrm{Cl}_{1,M}\text{ is conjugate degradable}\quad(M\ge1).
--   $$
--   Each assertion supplies one CPTP witness for the entire input operator space. The identity case $M=1$ is included.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 8, Theorem 1: conjugate degradability of two cloning families

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

/-- PDF pp.8–10, Theorem 1: both proven cloning families, retaining the M=1 identity case. -/
theorem cloningFamilies_conjugateDegradable :
    (∀ N : ℕ, 1≤N → ConjugateDegradable (clonerDilation N (N+1))) ∧
    (∀ M : ℕ, 1≤M → ConjugateDegradable (clonerDilation 1 M)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
