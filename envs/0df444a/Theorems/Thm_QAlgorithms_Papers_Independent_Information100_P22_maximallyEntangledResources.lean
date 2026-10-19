-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_maximallyEntangledResources
-- name    : QAlgorithms.Papers.Independent.Information100.P22.maximallyEntangledResources
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:49:05.393557+00:00
-- url     : https://prove2.me/theorems/18b32896-bd82-4d96-92e4-bd0022e2e5c7
-- title:
--   Corollary 1: Maximally entangled resources
-- statement:
--   For $m\ge2$, $k\ge1$, fix any ordered distinct Pauli axes and the corresponding sector encoder. Every normalized pure resource with $\rho_S=I/2^{mk}$ admits exact CPTP recovery from each prescribed $S_iN$ and completely depolarizing individual signal channels. Moreover,
--   $$m\text{ even and exact all-output recovery}\implies\rho_S=I/2^{mk}.$$
--   Thus maximal signal–key entanglement always suffices and is necessary in the even branch.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 5, Corollary 1: Maximally entangled resources

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Corollary 1, PDF p.5, proof p.24. -/
theorem maximallyEntangledResources (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R) :
    (rhoS R = mixed (Signals m k) →
      AllRecoverable R (twoPauliEncoder m k P Q) ∧ UniformlyConcealed R (twoPauliEncoder m k P Q)) ∧
    (Even m → AllRecoverable R (twoPauliEncoder m k P Q) → rhoS R = mixed (Signals m k)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
