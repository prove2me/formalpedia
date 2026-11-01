-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_nearestPauli_diamond
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.nearestPauli_diamond
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:56:56.723626+00:00
-- url     : https://prove2.me/theorems/84f00673-bb65-4a7a-b953-3599ddad6af9
-- title:
--   The same channel minimizes full diamond distance
-- statement:
--   Let $T=\operatorname{conv}\{(1,-1,1),(1,1,-1),(-1,-1,-1),(-1,1,1)\}$, $q\in T$, $0\le\eta\le1$, and $u\in\{0,1\}$. Let $P_q(x,y,z)=(q_1x,-q_2y,q_3z)$, let $A_\eta$ be amplitude damping, and put $E=X^u\circ A_\eta\circ P_q$, where $X$ denotes Pauli conjugation. Define $C$ by deleting the translation of $E$: its actual Bloch diagonal is $(\sqrt{1-\eta}q_1,-\sqrt{1-\eta}q_2,(1-\eta)q_3)$ when $u=0$ and $(\sqrt{1-\eta}q_1,\sqrt{1-\eta}q_2,-(1-\eta)q_3)$ when $u=1$. Then $C$ is Pauli and
--
--   $$\|E-C\|_\diamond=\eta,\qquad\eta\le\|E-P\|_\diamond\quad\text{for every Pauli channel }P.$$
--
--   Here the diamond distance is the supremum of the full output trace norm over normalized density matrices of a qubit input and a qubit reference, with the identity acting on the reference. The same explicit channel attains both minima, independently of a resource realization or uniqueness of the decomposition.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 9, Proposition 19

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.9--10,14--15, Proposition 19: the same explicit
channel attains the diamond minimum; the reference is a normalized qubit state. -/
theorem nearestPauli_diamond (u : Bool) (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (q : BlochCoordinates) (hq : q ∈ pauliTetrahedron) :
    IsPauli (closestPauli u eta q) ∧
    channelDiamondDistance (pauliDamping u eta q) (closestPauli u eta q) = eta ∧
    ∀ F : QubitMap, IsPauli F → eta ≤ channelDiamondDistance (pauliDamping u eta q) F := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
