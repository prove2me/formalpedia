-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_stabilization_impliesTriangularization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.stabilization_impliesTriangularization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:18:28.845161+00:00
-- url     : https://prove2.me/theorems/8e14c71e-d414-4e61-8b79-7c13ea7221fa
-- title:
--   Lemma 3.10: Stabilizability implies triangularizability
-- statement:
--   Let $G=-L$ be a GKSL generator on $\mathbb C^n$, $n\ge2$, whose reduced system stabilizes every simplex point. Then
--
--   $$\{V_k\}\text{ is simultaneously triangularizable}.$$
--
--   The conclusion applies to the given arbitrary representation, without a normality hypothesis.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 11, Lemma 3.10: Stabilizability implies triangularizability

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.11, Lemma 3.10: Stabilizability implies triangularizability.  -/
theorem stabilization_impliesTriangularization {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (h : stabilizableSystem D) : triangularizable (Set.range D.jump) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
