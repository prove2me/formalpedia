-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unital_stabilizationByType
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unital_stabilizationByType
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:33:32.497262+00:00
-- url     : https://prove2.me/theorems/b7553e76-039c-44cb-96b6-cd7ff798212a
-- title:
--   Theorem 5.6: Unital stabilizable states via algebra type
-- statement:
--   Let a GKSL generator on $\mathbb C^n$, $n\ge2$, be unital, and let $\lambda\in\Delta^{n-1}$. Then
--
--   $$\lambda\in\operatorname{stab}_R\quad\Longleftrightarrow\quad\operatorname{type}(G)\text{ refines the eigenvalue-multiplicity vector of }\lambda.$$
--
--   The type is determined by an actual unitary Wedderburn decomposition of the relaxation algebra. Multiplicities include zero eigenvalues. This characterizes the unital stabilizable set.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 24, Theorem 5.6: Unital stabilizable states via algebra type

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

/-- arXiv:2308.00561v1, PDF p.24, Theorem 5.6: Unital stabilizable states via algebra type. The type is not an arbitrary partition chosen to satisfy refinement: hasType pins the full algebra. All coordinate values, including zero, enter multiplicities. -/
theorem unital_stabilizationByType {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) (hu : unital D)
    (x : Vec n) (hx : x ∈ simplex n) :
    stabilizable D x ↔ ∃ tau : Multiset ℕ,
      hasType (relaxationAlgebra D.jump) tau ∧ refines tau (multiplicities x) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
