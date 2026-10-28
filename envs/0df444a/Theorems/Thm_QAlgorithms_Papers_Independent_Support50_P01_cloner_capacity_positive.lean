-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloner_capacity_positive
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloner_capacity_positive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:17:55.123988+00:00
-- url     : https://prove2.me/theorems/fe83f9a6-5c7c-49a5-84d4-3aeef005cd70
-- title:
--   §III.C: positive quantum capacity of all optimal qubit cloners
-- statement:
--   Let $1\le N\le M$ be integers. Let $\mathrm{Cl}_{N,M}$ be the specified optimal universal qubit cloner on $\operatorname{Sym}^N(\mathbb C^2)$, with receiver support $\operatorname{Sym}^M(\mathbb C^2)$ and environment dimension $M-N+1$. Its common dilation on normalized occupation kets is exactly Eqs.(21),(22). Write $\pi_d=I_d/d$, $I_c$ for coherent information in bits, $Q^{(1)}$ for its supremum over all density inputs, and $Q$ for its regularization over all positive block lengths and arbitrary entangled block inputs. All these optimal cloners satisfy
--   $$Q(\mathrm{Cl}_{N,M})>0.$$
--   The general positivity statement does not require the unproved general conjugate-degradability conjecture.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 11, §III.C: positive quantum capacity of all optimal qubit cloners

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

/-- PDF p.11: all optimal cloners have positive capacity, without the general conjecture. -/
theorem cloner_capacity_positive (N M : ℕ) (hN : 1≤N) (hNM : N≤M) :
    0 < quantumCapacity (receiverChannel (clonerDilation N M)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
