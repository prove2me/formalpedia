-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloningFamilies_capacity
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloningFamilies_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:17:11.31399+00:00
-- url     : https://prove2.me/theorems/c7eb5dcf-908f-4f94-912e-548fe633a637
-- title:
--   §III.C: exact capacities for N→N+1 and 1→M
-- statement:
--   Let $1\le N\le M$ be integers. Let $\mathrm{Cl}_{N,M}$ be the specified optimal universal qubit cloner on $\operatorname{Sym}^N(\mathbb C^2)$, with receiver support $\operatorname{Sym}^M(\mathbb C^2)$ and environment dimension $M-N+1$. Its common dilation on normalized occupation kets is exactly Eqs.(21),(22). Write $\pi_d=I_d/d$, $I_c$ for coherent information in bits, $Q^{(1)}$ for its supremum over all density inputs, and $Q$ for its regularization over all positive block lengths and arbitrary entangled block inputs. The exact regularized capacities of the two established families are
--   $$
--   Q(\mathrm{Cl}_{N,N+1})=\log_2\frac{N+2}{2}\quad(N\ge1),\qquad
--   Q(\mathrm{Cl}_{1,M})=\log_2\frac{M+1}{M}\quad(M\ge1).
--   $$
--   These identities use conjugate degradability only where the source establishes it.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 11, §III.C: exact capacities for N→N+1 and 1→M

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

/-- PDF p.11: exact capacities only for the two established conjugate degradable families. -/
theorem cloningFamilies_capacity :
    (∀ N : ℕ, 1≤N → quantumCapacity (receiverChannel (clonerDilation N (N+1))) =
      Real.logb 2 ((N+2 : ℝ)/2)) ∧
    (∀ M : ℕ, 1≤M → quantumCapacity (receiverChannel (clonerDilation 1 M)) =
      Real.logb 2 ((M+1 : ℝ)/M)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
