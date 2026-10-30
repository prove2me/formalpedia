-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_quaternion_entanglementBreaking
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.quaternion_entanglementBreaking
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:02:21.220675+00:00
-- url     : https://prove2.me/theorems/29f4f090-25d3-4062-8ddc-146c5e44d8dd
-- title:
--   Section 8.5, Eq.(155): quaternion entanglement-breaking region
-- statement:
--   For the concrete quaternion family $\Phi_{a,b,c}$ with real $a,b,c$, being a CPTP entanglement-breaking channel is equivalent to all eight inequalities
--
--   $$
--   \begin{gathered}1+a+b+c\ge0,\quad1+a-b-c\ge0,\quad1-a+b-c\ge0,\quad1-a-b+c\ge0,\\1-a-b-c\ge0,\quad1+a+b-c\ge0,\quad1+a-b+c\ge0,\quad1-a+b+c\ge0.\end{gathered}
--   $$
--
--   The first four are CP and the last four are PPT. Within the CP domain, PPT is equivalent to separability of the unnormalized Choi matrix in the positive cone, or of $J/2$ as a density matrix. The EB predicate quantifies over all positive finite ancilla dimensions and all bipartite input states.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 31, Section 8.5, Eq.(155): quaternion entanglement-breaking region

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF pp.30--31 Eq.(155), together with the four CP inequalities Eq.(129).
All eight inequalities are retained, rather than replacing the channel region by a cube. -/
theorem quaternion_entanglementBreaking (a b c : ℝ) :
    ((IsPaperChannel (quaternionMap a b c) ∧
        QAlgorithms.Entanglement.IsEntanglementBreakingPositive (quaternionMap a b c)) ↔
      QuaternionCP a b c ∧ QuaternionPPT a b c) ∧
    (QuaternionCP a b c →
      (QAlgorithms.Entanglement.IsSeparablePositive (choi (quaternionMap a b c)) ↔
        (QAlgorithms.Entanglement.partialTransposeFirst (choi (quaternionMap a b c))).PosSemidef) ∧
      ((QAlgorithms.Entanglement.partialTransposeFirst (choi (quaternionMap a b c))).PosSemidef ↔
        QuaternionPPT a b c)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
