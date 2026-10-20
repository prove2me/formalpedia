-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem23
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem23
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:50:50.961643+00:00
-- url     : https://prove2.me/theorems/834d1b39-1272-4642-b6ec-d3002e362dd8
-- title:
--   Theorem 23 (Indivisible qubit channels)
-- statement:
--   Let $T$ be a CPTP map on $M_2(\mathbb C)$, a qubit channel. Composition applies the rightmost factor first; map norms are induced Hilbert–Schmidt norms. Assume $T$ is not a unitary conjugation. Then
--
--   $$T\text{ is indivisible within CPTP}\iff\operatorname{rank}J(T)=3\text{ and }T\text{ has a diagonal Lorentz normal form}.$$
--
--   A diagonal Lorentz normal form is a CPTP representative under invertible single-Kraus CP pre- and post-filters whose full Pauli representation is unital and has a diagonal real $3\times3$ block.
--
--   This characterizes all nonunitary indivisible qubit channels; unitary channels are excluded explicitly.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 19, Theorem 23 (Indivisible qubit channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 23, PDF pp.19--20: the explicit nonunitary hypothesis excludes rank-one unitary channels. -/
theorem theorem23 (T : Super 2) (hT : Channel T) (hunitary : ¬ IsUnitaryConjugation T) :
    Indivisible true T ↔ krausRank T = 3 ∧ HasDiagonalNormalForm T := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
