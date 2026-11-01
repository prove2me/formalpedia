-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P45_pathSuccess
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P45.pathSuccess
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:24:01.090017+00:00
-- url     : https://prove2.me/theorems/92f5bf64-6002-407a-95b9-9151790f1258
-- title:
--   A fixed chain: unconditional one-slot success probability
-- statement:
--   Fix a chain of $k\ge1$ edges and prescribe its $k-1$ internal Bell-state measurements before the success flags are observed. External links independently produce perfect EPR pairs with probability $p\in[0,1]$, and the prescribed BSMs have independent heralded success probability $q\in[0,1]$, independent of the external attempts. Memories last one slot, each is used at most once, and the two terminals retain their halves. The probability $P_k$ of delivering one ebit after the external and internal phases, and hence its expected delivered count per slot, is
--
--   $$P_k=p^kq^{k-1}.$$
--
--   This is the unconditional linear-chain rate; it includes external failures, unlike the conditional path yields in global routing.
-- source:
--   Routing entanglement in the quantum internet, arXiv:1708.07142v2, PDF p. 4, §II.A and §II.B.2: single-chain success probability and rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45

namespace QAlgorithms.Papers.Independent.Intakethird100.P45

open scoped BigOperators

noncomputable section

/-- PDF pp.4,7: the fixed `k`-edge chain delivers one ebit with probability
`p^k q^(k-1)`, also its expected delivered count. Terminals do not swap. -/
theorem pathSuccess (k : ℕ) (hk : 0 < k) (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    chainProbability k p q = p ^ k * q ^ (k - 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P45
