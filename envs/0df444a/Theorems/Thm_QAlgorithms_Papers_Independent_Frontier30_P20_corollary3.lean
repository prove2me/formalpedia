-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_corollary3
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.corollary3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:33:15.196987+00:00
-- url     : https://prove2.me/theorems/66f18559-976a-45c1-9728-e8ce6209a3a8
-- title:
--   Corollary 3 (Monotonicity of the determinant)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. A map $T$ and an actual two-sided inverse are both positive and trace preserving if and only if $T$ is a unitary conjugation or a transposition up to unitary equivalence. For positive trace-preserving $T,R$,
--
--   $$|\det(TR)|\le|\det T|,$$
--
--   with equality exactly when $R$ is a unitary conjugation, $R$ is a transposition up to unitary equivalence, or $\det T=0$.
--
--   The equality clause detects reversible factors and singular endpoints.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 7, Corollary 3 (Monotonicity of the determinant)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Corollary 3, PDF p.7: actual positive TP inverse and strict determinant monotonicity. -/
theorem corollary3 {d : ℕ} (hd : 0 < d) :
    (∀ T : Super d,
      (InClass false T ∧ ∃ S : Super d, InClass false S ∧ S * T = 1 ∧ T * S = 1) ↔
        IsUnitaryConjugation T ∨ TransposeEquivalent T) ∧
    (∀ T R : Super d, InClass false T → InClass false R →
      |determinant (T * R)| ≤ |determinant T| ∧
      (|determinant (T * R)| = |determinant T| ↔
        IsUnitaryConjugation R ∨ TransposeEquivalent R ∨ determinant T = 0)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
