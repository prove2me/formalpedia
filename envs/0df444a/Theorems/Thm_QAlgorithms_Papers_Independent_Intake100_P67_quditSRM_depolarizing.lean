-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_quditSRM_depolarizing
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.quditSRM_depolarizing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:24:45.330507+00:00
-- url     : https://prove2.me/theorems/8733b9cd-c72f-4a4a-bab6-094acaf0a4e6
-- title:
--   The completed qudit SRM channel is depolarizing
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers and let $\Lambda$ be the correction-free teleportation channel obtained from the positive maximally entangled resource $|\phi^+\rangle^{\otimes N}$ and exactly the completed SRM. There is a real parameter $t$ such that
--
--   $$0\le t\le\frac{d^2}{d^2-1},\qquad\Lambda(T)=(1-t)T+\frac{t}{d}\operatorname{tr}(T)I_d$$
--
--   for every complex $d\times d$ operator $T$.
--
--   The reference and resource use the same positive maximally entangled vector. The parameter is the noise fraction in the accepted depolarizing map. Its interval is the completely positive domain, rather than a separate fidelity optimization claim.
--
--   This identifies the full channel, including its action on off-diagonal operators.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 6, §IV A, paragraph preceding §IV B

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF p.6, §IV A: the completed qudit SRM channel is depolarizing.
The parameter is the accepted map's noise fraction, not its retained-signal fraction. -/
theorem quditSRM_depolarizing (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) ∧
      quditChannel N d = QuditFidelity.depolarizingMap d (by omega) t := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
