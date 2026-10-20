-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_threeStateZeroCommunication
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.threeStateZeroCommunication
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:32:08.714659+00:00
-- url     : https://prove2.me/theorems/6caa0626-b92b-479c-888f-8a92e33f4570
-- title:
--   Zero-communication randomness for the three-state ensemble
-- statement:
--   Let $E_3$ be the ensemble with equal probabilities $1/3$ of $|0\rangle$, $(|0\rangle+|1\rangle)/\sqrt2$, and $|2\rangle$ on a three-dimensional system. Alice holds the label and Bob the state. In the iid one-way common-randomness model, where the rate is defined by vanishing disagreement and Shannon key entropy, let $C(E_3,0)$ be the capacity without communication. With $h_2$ the binary entropy in bits,
--
--   $$C(E_3,0)\ge h_2(1/3).$$
--
--   This is an exact analytic lower bound from the perfectly distinguishable partition of the third state and the first two states.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 12, §2, three-state illustration: an explicit zero-communication CR rate

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

/-- PDF p.12, three-state illustration: the perfectly distinguishable partition gives h2(1/3)
bits of common randomness without communication. -/
theorem threeStateZeroCommunication :
    binEntropy2 (1/3) ≤ crCapacity (cqDensity threeStateEnsemble) 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P07

end
