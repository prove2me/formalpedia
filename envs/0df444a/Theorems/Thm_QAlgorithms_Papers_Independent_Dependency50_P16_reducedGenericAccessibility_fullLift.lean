-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_reducedGenericAccessibility_fullLift
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.reducedGenericAccessibility_fullLift
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:49:19.014986+00:00
-- url     : https://prove2.me/theorems/87c1661f-1d58-4bf0-b9a0-9eae03ad2daa
-- title:
--   Unnumbered full-system accessibility consequence
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, with a fixed fully Lie-generating Hamiltonian-control family, generic direct accessibility of (R) implies
--
--   $$\text{generic accessibility of the full bilinear system (B)}.$$
--
--   Both genericity predicates require an open dense subset of full relative measure. As the source says, the implication applies as in the nonunital case as well.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 27, Unnumbered full-system accessibility consequence

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

/-- arXiv:2308.00561v1, PDF p.27, Unnumbered full-system accessibility consequence. No redundant unitality hypothesis is added: the printed implication explicitly extends the nonunital case. FullControls carries the Lie-generation and trajectory definitions carry real locally integrable controls. -/
theorem reducedGenericAccessibility_fullLift {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (C : FullControls n) (h : genericallyDirectlyAccessible D) : genericallyAccessibleB D C := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
