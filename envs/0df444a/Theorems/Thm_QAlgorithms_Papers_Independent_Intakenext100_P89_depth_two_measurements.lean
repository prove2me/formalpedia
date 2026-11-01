-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P89_depth_two_measurements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P89.depth_two_measurements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:29:44.481998+00:00
-- url     : https://prove2.me/theorems/6e236a41-71fd-4649-90e5-ced55c66ac84
-- title:
--   Depth-two tree: logical X and Z success probabilities
-- statement:
--   Consider a regular tree with positive integer branching factors $b_0,b_1$. Every physical photon used in a measurement independently survives with probability $p=1-\epsilon_{\rm stat}\in[0,1]$. The tree has $b_0$ child groups, each comprising a child and its $b_1$ grandchildren. Logical $X$ succeeds if at least one group survives completely. Logical $Z$ succeeds if every group contains at least one surviving photon, allowing the child to be measured directly or indirectly. Then
--
--   $$P_X=1-(1-p^{b_1+1})^{b_0},\qquad P_Z=\left[1-(1-p)^{b_1+1}\right]^{b_0}.$$
--
--   These are the depth-two specializations of the indirect-measurement recursion. For the source's repeater, $p=e^{-\alpha L/n}P_{\rm chip}^{k+2}P_{\rm fib}\eta_{\rm GHZ}\eta_c$. No optimality of depth two is assumed.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, PDF p. 11, IV, Eqs.(5)–(6): depth-two logical measurement probabilities

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Source p.11, IV, Eqs.(2)--(6): the depth-two specialization of the indirect-measurement
recursion with positive integral branches. Here p = 1-epsilon_stat is photon survival.
No optimality of depth two is asserted or assumed. -/
theorem depth_two_measurements (b0 b1 : ℕ) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    depthTwoLogicalXSuccess b0 b1 p = 1 - (1 - p ^ (b1 + 1)) ^ b0 ∧
    logicalZ b0 b1 p = (1 - (1 - p) ^ (b1 + 1)) ^ b0 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P89
