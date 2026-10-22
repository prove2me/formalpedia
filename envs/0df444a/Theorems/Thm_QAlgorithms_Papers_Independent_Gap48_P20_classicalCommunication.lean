-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_classicalCommunication
-- name    : QAlgorithms.Papers.Independent.Gap48.P20.classicalCommunication
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:08:38.607246+00:00
-- url     : https://prove2.me/theorems/f7e61a39-a186-4ccb-b14f-2a63d01c0fa5
-- title:
--   Optimal classical communication with unlimited entanglement
-- statement:
--   Let $|\psi\rangle^{ACBR}$ be normalized and pure on nonzero finite registers. Alice retains $A$ while transferring $C$ to Bob, who initially holds $B$, with the complete source including $R$ preserved. Use entropy in bits. With unlimited Bell assistance and local CPTP operations, only a forward classical channel is available. Its optimal asymptotic rate is
--   $$
--   c_*=I(R;C\mid A)=I(C;R\mid B).
--   $$
--   More precisely a real classical rate $c$ is achievable if and only if $c\ge c_*$. Here, for every positive error and rate slack, every sufficiently large positive blocklength has an entirely classical message of at most $n(c+\delta)$ bits, unrestricted initial and final Bell counts, and vanishing joint full trace-norm reconstruction error. There is also a protocol family attaining the pair
--   $$
--   (c,E)=(c_*,H(C\mid B)),\qquad c_*\le I(RA;C).
--   $$
--   Classical messages are enforced by complete dephasing of the transmitted register on every encoder input. No quantum channel is free. This improves the merging scenario that places $A$ in the inaccessible reference.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, PDF p. 3, classical-communication

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, application (4): the optimal classical rate with unrestricted Bell
assistance is QCMI. Teleportation achieves that rate with net ebit cost H(C|B).
Alice retains A; the older I(RA;C) rate is included only for comparison. -/
theorem classicalCommunication {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi) :
    (∀ c : ℝ, ClassicalAchievable psi c ↔ 2 * quantumCost psi ≤ c) ∧
    ClassicalPairAchievable psi (2 * quantumCost psi) (conditionalCost psi) ∧
    2 * quantumCost psi = 2 * quantumCost (swappedSource psi) ∧
    2 * quantumCost (swappedSource psi) ≤ mergingClassicalCost psi := by sorry

end QAlgorithms.Papers.Independent.Gap48.P20

end
