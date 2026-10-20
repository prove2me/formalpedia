-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem2
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:32:07.619985+00:00
-- url     : https://prove2.me/theorems/ec4c8f34-3b8c-4a8e-9ae6-b3b6189cbe34
-- title:
--   Theorem 2 (Determinants)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Let $T$ be positive and trace preserving. Its complex determinant is real, and
--
--   $$-1\le\det T\le1,\qquad |\det T|=1\iff T\text{ is unitary conjugation or transposition up to unitary equivalence}.$$
--
--   Unitary conjugation has determinant one, and determinant minus one forces the transposition class. Every member of the latter class has determinant $(-1)^{d(d-1)/2}$. Thus, for $d\ge2$, both classification converses hold precisely when $\lfloor d/2\rfloor$ is odd. In dimension one the classes coincide.
--
--   This characterizes the extremal determinant magnitudes without assuming complete positivity.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 6, Theorem 2 (Determinants)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 2, PDF pp.6--7: determinants of positive TP maps.
The sign formula records the parity clause without the false d=1 converse-failure reading. -/
theorem theorem2 {d : ℕ} (hd : 0 < d) (T : Super d) (hT : InClass false T) :
    (complexDet T).im = 0 ∧ -1 ≤ determinant T ∧ determinant T ≤ 1 ∧
    (|determinant T| = 1 ↔ IsUnitaryConjugation T ∨ TransposeEquivalent T) ∧
    (IsUnitaryConjugation T → determinant T = 1) ∧
    (determinant T = -1 → TransposeEquivalent T) ∧
    (TransposeEquivalent T → determinant T = (-1 : ℝ) ^ (d * (d - 1) / 2)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
