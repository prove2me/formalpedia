-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_amplitudeDamping_selfSimulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.amplitudeDamping_selfSimulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:55:28.369067+00:00
-- url     : https://prove2.me/theorems/9ca6c349-cf21-45c2-9b2a-1cff7f812dec
-- title:
--   Amplitude damping cannot teleport itself except at endpoints
-- statement:
--   For $0\le\gamma\le1$, let $A_\gamma$ be amplitude damping and $\chi_\gamma$ its normalized two-qubit Choi state. In the fixed Bell-measurement protocol with Pauli corrections and arbitrary conditional classical communication,
--
--   $$A_\gamma\text{ is simulable over }\chi_\gamma\quad\Longleftrightarrow\quad\gamma\in\{0,1\}.$$
--
--   Thus self-simulation fails for $0<\gamma<1$. Identity teleportation realizes the zero endpoint, and a correction supported on $I,Z$ realizes the reset channel at one. The assertion concerns this specified noisy-teleportation protocol.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 8, Consequence following Theorem 16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF p.8, paragraph following Theorem 16.
Both printed exceptions are included positively; this is only the Bell/Pauli protocol. -/
theorem amplitudeDamping_selfSimulation (gamma : ℝ) (h0 : 0 ≤ gamma) (h1 : gamma ≤ 1) :
    Simulable (normalizedQubitChoi (blochAmplitudeDamping gamma)) (blochAmplitudeDamping gamma) ↔
      gamma = 0 ∨ gamma = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
