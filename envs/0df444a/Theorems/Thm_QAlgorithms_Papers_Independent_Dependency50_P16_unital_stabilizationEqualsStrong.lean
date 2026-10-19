-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unital_stabilizationEqualsStrong
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unital_stabilizationEqualsStrong
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:33:00.999511+00:00
-- url     : https://prove2.me/theorems/009e92f9-1691-4add-8fe8-e37e08c701d5
-- title:
--   Lemma 5.5: Stabilizability equals strong stabilizability for unital generators
-- statement:
--   For a unital GKSL generator on $\mathbb C^n$, $n\ge2$,
--
--   $$\operatorname{stab}_R=\{\lambda\in\Delta^{n-1}:0\in\operatorname{derv}(\lambda)\}.$$
--
--   Thus every relaxed stabilizable point is already strongly stabilizable by one induced field.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 24, Lemma 5.5: Stabilizability equals strong stabilizability for unital generators

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

/-- arXiv:2308.00561v1, PDF p.24, Lemma 5.5: Stabilizability equals strong stabilizability for unital generators.  -/
theorem unital_stabilizationEqualsStrong {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (h : unital D) : {x | stabilizable D x} = {x | stronglyStabilizable D x} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
