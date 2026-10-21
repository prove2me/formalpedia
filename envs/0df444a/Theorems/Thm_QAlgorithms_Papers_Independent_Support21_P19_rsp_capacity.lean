-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_rsp_capacity
-- name    : QAlgorithms.Papers.Independent.Support21.P19.rsp_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:07:35.54209+00:00
-- url     : https://prove2.me/theorems/fa5afd23-0a11-4811-a2cd-f4430139229c
-- title:
--   Corollary 3 (RSP capacity of unitary gates)
-- statement:
--   Let $U$ be a finite-dimensional bipartite unitary gate. If its unassisted forward classical achievable rate is $C\ge0$, then its unassisted restricted block remote-preparation rate is at least $C$:
--
--   $$
--   U\ge C\,[c\to c]\ (a)\quad\Longrightarrow\quad U\ge C\text{ remote qubits}\ (a).
--   $$
--
--   For every positive error and rate slack and all sufficiently large $n$, at most $n$ calls of $U$ prepare $m$ independently known $m$-qubit pure states with $m^2\ge n(C-\delta)$ and uniform vanishing error. Bob's operations are independent of the states, and there is zero external entanglement seed. The case $C=0$ allows the empty remote task. The result inherits the block task of Eq. (5), rather than full arbitrary-state remote preparation.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 3, Corollary 3 (RSP capacity of unitary gates)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Corollary 3: the source's restricted block RSP task, for bipartite unitary gates. -/
theorem rsp_capacity (U : Resource) (hU : IsUnitaryResource U) (C : ℝ)
    (h : AchievesTransmission U (cbitChannel 2) C 0) : RemoteRate U C 0 := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
