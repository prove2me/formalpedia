-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_dephasingTimeSharingGain
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.dephasingTimeSharingGain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:56:44.812156+00:00
-- url     : https://prove2.me/theorems/9c861f67-4232-432e-b3a1-fd165871379a
-- title:
--   dephasing-time-sharing-gain
-- statement:
--   For every qubit dephasing channel with parameter $0<p<1$, let $F_{CQ}(\mu)$ and $F_{CE}(\mu)$ be the coordinate families in the corresponding explicit capacity formula, with $0\le\mu\le1/2$. Define $T_{CQ}$ by time sharing between $F_{CQ}(0)$ and $F_{CQ}(1/2)$ and lowering both rates; define $T_{CE}$ by time sharing between $F_{CE}(0)$ and $F_{CE}(1/2)$, lowering $C$ and permitting extra consumption $E$. Then
--   $$T_{CQ}\subsetneq\mathcal C_{CQ},\qquad T_{CE}\subsetneq\mathcal C_{CE}.$$
--   Both resource regions strictly improve on their own endpoint time-sharing strategy. Properness requires an interior improvement; no strict improvement is asserted at the endpoints. The noiseless case is excluded.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 12, dephasing-time-sharing-gain

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P24
  (Dilation PhysicalDilation ChannelEB Hadamard EqualMax AdditiveMax
   dephasingDilation dephasingGamma cloningDilation)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)

open QAlgorithms.Papers.Independent.Information100.P32 (diagonal)

open QAlgorithms.Papers.Independent.Dependency50.P24 (ensembleHolevoBits)

open QAlgorithms.Papers.Independent.Gap48.P44 (cqTimeSharing ceTimeSharing)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E]

variable [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- PDF p.12: strict improvement in BOTH two-resource scenarios, only for 0<p<1. -/
theorem dephasingTimeSharingGain (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    cqTimeSharing (dephasingCQ p 0).1 (dephasingCQ p (1/2)).2 ⊂
      capacityCQ (dephasingDilation p) ∧
    ceTimeSharing (dephasingCE p 0).1 (dephasingCE p (1/2)).1
      (dephasingCE p (1/2)).2 ⊂
      capacityCE (dephasingDilation p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
