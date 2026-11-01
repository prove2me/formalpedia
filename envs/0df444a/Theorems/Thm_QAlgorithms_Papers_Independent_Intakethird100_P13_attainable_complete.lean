-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_attainable_complete
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.attainable_complete
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:54:31.721235+00:00
-- url     : https://prove2.me/theorems/6c237667-5a35-4531-9982-ec98cae9bef6
-- title:
--   Complete attainable Pauli-damping region, including endpoints
-- statement:
--   Let $A_\gamma$ denote amplitude damping, $\chi_\gamma=(\mathrm{id}\otimes A_\gamma)(|\Phi^+\rangle\langle\Phi^+|)$ its normalized Choi state, and $P_q$ the Pauli map with Bloch action $(x,y,z)\mapsto(q_1x,-q_2y,q_3z)$. For $0<\gamma<1$, a qubit quantum channel $E$ is simulable by noisy Bell/Pauli teleportation over $\chi_\gamma$ if and only if
--
--   $$E=X^u\circ A_\eta\circ P_q,\qquad u\in\{0,1\},\quad0\le\eta\le\gamma,\quad q\in\operatorname{conv}(V_{\gamma,\eta}),$$
--
--   where $X$ denotes conjugation by the Pauli $X$, $a=\sqrt{(1-\gamma)/(1-\eta)}$, $b=1-\eta/\gamma$, and the eight vertices are
--
--   $$V_{\gamma,\eta}=\{(a,\pm ab,\mp a^2b),(\pm ab,a,\mp a^2b),(-a,\pm ab,\pm a^2b),(\pm ab,-a,\pm a^2b)\}.$$
--
--   Signs within each triple are paired. At $\gamma=0$ the simulable channels are exactly all Pauli channels. At $\gamma=1$ they are exactly the input-independent diagonal states with Bloch vector $(0,0,z)$, $-1\le z\le1$. This characterizes the whole attainable set without asserting uniqueness of parameters.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 7, Theorem 16, Eqs.(59)–(67)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.7--8, Theorem 16, converse paragraph and vertex proof.
Corrected endpoint clauses use the physical simulator rather than undefined 0/0 vertices.
No decomposition uniqueness is asserted. -/
theorem attainable_complete :
    (∀ gamma : ℝ, 0 < gamma → gamma < 1 → ∀ E : QubitMap, IsChannel E →
      (Simulable (normalizedQubitChoi (blochAmplitudeDamping gamma)) E ↔
        ∃ u : Bool, ∃ eta : ℝ, ∃ q : BlochCoordinates,
          0 ≤ eta ∧ eta ≤ gamma ∧ q ∈ attainableRegion gamma eta ∧
          E = pauliDamping u eta q)) ∧
    (∀ E : QubitMap, IsChannel E →
      (Simulable (normalizedQubitChoi (blochAmplitudeDamping 0)) E ↔ IsPauli E)) ∧
    (∀ E : QubitMap, IsChannel E →
      (Simulable (normalizedQubitChoi (blochAmplitudeDamping 1)) E ↔
        ∃ z : ℝ, -1 ≤ z ∧ z ≤ 1 ∧ E = axialReplacement z)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
