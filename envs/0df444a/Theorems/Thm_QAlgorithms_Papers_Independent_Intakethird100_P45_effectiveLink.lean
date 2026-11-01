-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P45_effectiveLink
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P45.effectiveLink
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:23:20.859373+00:00
-- url     : https://prove2.me/theorems/62ebd536-11bf-45b9-b15d-52663260b899
-- title:
--   Parallel attempts: probability of one usable external link
-- statement:
--   Assume the paper's heralded-loss model: a successful elementary attempt produces a perfect EPR pair. Let $S\ge1$ independent optical attempts across one physical edge each succeed with probability $p_0\in[0,1]$. The neighboring repeaters retain at most one successful pair, discarding additional successes. Then the probability $p$ of a usable external link in that slot is
--
--   $$p=1-(1-p_0)^S.$$
--
--   This reduces parallel optical attempts to the single-pair-per-edge model used by the routing protocols.
-- source:
--   Routing entanglement in the quantum internet, arXiv:1708.07142v2, PDF p. 4, §II.A: parallel optical attempts give the effective link probability

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45

namespace QAlgorithms.Papers.Independent.Intakethird100.P45

open scoped BigOperators

noncomputable section

/-- PDF p.4: the usable-link probability is `1-(1-p0)^S`, including `p0=0,1`. -/
theorem effectiveLink (S : ℕ) (hS : 0 < S) (p0 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 ≤ 1) :
    retainedLinkProbability S p0 = 1 - (1 - p0) ^ S := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P45
