-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_cloningTimeSharingGain
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.cloningTimeSharingGain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:57:36.942967+00:00
-- url     : https://prove2.me/theorems/659177b8-3a3d-4c6e-8386-7f3d09d4a6b3
-- title:
--   cloning-time-sharing-gain
-- statement:
--   For every universal symmetric-output cloning channel with parameter $N>1$ (integer $N$ in the cloning case), let $F_{CQ}(\mu)$ and $F_{CE}(\mu)$ be the coordinate families in the corresponding explicit capacity formula, with $0\le\mu\le1/2$. Define $T_{CQ}$ by time sharing between $F_{CQ}(0)$ and $F_{CQ}(1/2)$ and lowering both rates; define $T_{CE}$ by time sharing between $F_{CE}(0)$ and $F_{CE}(1/2)$, lowering $C$ and permitting extra consumption $E$. Then
--   $$T_{CQ}\subsetneq\mathcal C_{CQ},\qquad T_{CE}\subsetneq\mathcal C_{CE}.$$
--   Both resource regions strictly improve on their own endpoint time-sharing strategy. Properness requires an interior improvement; no strict improvement is asserted at the endpoints. The noiseless case is excluded.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 15, cloning-time-sharing-gain

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

/-- PDF pp.14--15: BOTH cloning resource regions strictly beat their endpoint time sharing. -/
theorem cloningTimeSharingGain (N : ℕ) (hN : 1 < N) :
    cqTimeSharing (cloningCQ N 0).1 (cloningCQ N (1/2)).2 ⊂
      capacityCQ (cloningDilation N) ∧
    ceTimeSharing (cloningCE N 0).1 (cloningCE N (1/2)).1
      (cloningCE N (1/2)).2 ⊂
      capacityCE (cloningDilation N) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
