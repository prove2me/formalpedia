-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_nearestPauli_trace
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.nearestPauli_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:56:12.722009+00:00
-- url     : https://prove2.me/theorems/94f1c573-a2d4-4dcc-a9bb-9f1a9316526c
-- title:
--   Explicit nearest Pauli channel in the full trace norm
-- statement:
--   Let $T=\operatorname{conv}\{(1,-1,1),(1,1,-1),(-1,-1,-1),(-1,1,1)\}$, $q\in T$, $0\le\eta\le1$, and $u\in\{0,1\}$. Let $P_q(x,y,z)=(q_1x,-q_2y,q_3z)$, let $A_\eta$ be amplitude damping, and put $E=X^u\circ A_\eta\circ P_q$, where $X$ denotes Pauli conjugation. Define $C$ by deleting the translation of $E$: its actual Bloch diagonal is $(\sqrt{1-\eta}q_1,-\sqrt{1-\eta}q_2,(1-\eta)q_3)$ when $u=0$ and $(\sqrt{1-\eta}q_1,\sqrt{1-\eta}q_2,-(1-\eta)q_3)$ when $u=1$. Then $C$ is a Pauli channel and
--
--   $$\|E-C\|_1=\eta,\qquad\eta\le\|E-P\|_1\quad\text{for every Pauli channel }P,$$
--
--   where $\|E-F\|_1=\sup_{\rho\ge0,\,\operatorname{Tr}\rho=1}\|E(\rho)-F(\rho)\|_1$ uses the full matrix trace norm. This gives explicit attainment, without claiming that the minimizer is unique.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 9, Proposition 18

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.9,14, Proposition 18: explicit attainment and
comparison against every Pauli competitor, with full trace norm and no uniqueness. -/
theorem nearestPauli_trace (u : Bool) (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (q : BlochCoordinates) (hq : q ∈ pauliTetrahedron) :
    IsPauli (closestPauli u eta q) ∧
    channelTraceDistance (pauliDamping u eta q) (closestPauli u eta q) = eta ∧
    ∀ F : QubitMap, IsPauli F → eta ≤ channelTraceDistance (pauliDamping u eta q) F := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
