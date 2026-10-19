-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_eigenvectors_boundFlowRatio
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.eigenvectors_boundFlowRatio
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:23:18.232973+00:00
-- url     : https://prove2.me/theorems/ffb80ae1-6049-465a-9543-a66daa60db65
-- title:
--   Lemma 4.5: Uniform bound on the one-dimensional flow ratio
-- statement:
--   Let $V_1,\ldots,V_r\in\mathbb C^{n\times n}$, $n\ge2$, be a finite family such that every common right eigenvector is also a common eigenvector of all adjoints. There is a family-dependent constant $C>0$ such that
--
--   $$\frac{\sum_{i=2}^nJ_{1i}(U)}{\sum_{i=2}^nJ_{i1}(U)}\le C\qquad(U\in SU(n),\ \sum_{i=2}^nJ_{i1}(U)>0).$$
--
--   No common eigenvector is assumed to exist. This is a uniform bound on defined real flow ratios.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 14, Lemma 4.5: Uniform bound on the one-dimensional flow ratio

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

/-- arXiv:2308.00561v1, PDF p.14, Lemma 4.5: Uniform bound on the one-dimensional flow ratio. The proof explicitly restricts this real quotient to positive outflow. C precedes U, and r=0 is permitted; the quotient domain is then empty. -/
theorem eigenvectors_boundFlowRatio {n r : ℕ} (hn : 2 ≤ n) (V : Fin r → Mat n)
    (h : eigenvectorObstruction V) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Mat n, specialUnitary U →
      0 < outflow V 1 U → inflow V 1 U / outflow V 1 U ≤ C := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
