-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_zeroCommunication
-- name    : QAlgorithms.Papers.Independent.Gap48.P20.zeroCommunication
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:07:49.970081+00:00
-- url     : https://prove2.me/theorems/fa572ee2-38ca-4165-af63-5569b3c56f60
-- title:
--   Zero communication rate and equality in strong subadditivity
-- statement:
--   Let $|\psi\rangle^{ACBR}$ be a normalized pure state on nonzero finite registers, with Alice holding $AC$, Bob holding $B$, and neither party acting on $R$. Entropies are measured in bits. Allow arbitrary local CPTP operations, Bell-pair consumption or generation, and forward qubits counted at their actual rate. Then
--   $$
--   \exists E\in\mathbb R:\ (0,E)\text{ is achievable}\quad\Longleftrightarrow\quad I(C;R\mid B)=0.
--   $$
--   Achievability uses independent copies, vanishing full trace-norm error on the source jointly with all returned Bell pairs, and arbitrarily small positive rate slack at every sufficiently large positive blocklength. In particular zero communication rate permits sublinear communication; it does not mean every finite-block protocol sends no messages.
--
--   This characterizes the operational zero-rate boundary. The cited structural characterization and the following printed entanglement-cost formula are separate statements.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, PDF p. 3, zero-communication

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, application (3): zero rate, allowing sublinear messages, is equivalent
to equality in strong subadditivity. The flagged structural theorem is cited
background, and the following printed entanglement formula is deferred separately. -/
theorem zeroCommunication {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi) :
    (∃ E : ℝ, RedistributionAchievable psi 0 E) ↔ 2 * quantumCost psi = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P20

end
