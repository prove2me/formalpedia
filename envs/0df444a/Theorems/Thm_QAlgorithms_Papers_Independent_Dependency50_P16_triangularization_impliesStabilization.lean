-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_triangularization_impliesStabilization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.triangularization_impliesStabilization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:19:03.417671+00:00
-- url     : https://prove2.me/theorems/4c66fefa-728a-4bf0-a1f2-c9a0a5b8902d
-- title:
--   Lemma 3.11: Triangularizability implies stabilizability
-- statement:
--   Let $G=-L$ be a GKSL generator on $\mathbb C^n$, $n\ge2$. If one common invertible change of basis makes all its jumps upper triangular, then
--
--   $$\forall\lambda\in\Delta^{n-1},\quad0\in\operatorname{conv}\{-L_U\lambda:U\in SU(n)\}.$$
--
--   Thus simultaneous triangularizability implies stabilization of the whole reduced system.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 11, Lemma 3.11: Triangularizability implies stabilizability

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

/-- arXiv:2308.00561v1, PDF p.11, Lemma 3.11: Triangularizability implies stabilizability.  -/
theorem triangularization_impliesStabilization {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (h : triangularizable (Set.range D.jump)) : stabilizableSystem D := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
