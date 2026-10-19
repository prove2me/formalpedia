-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_algebraType_refinesBlocks
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.algebraType_refinesBlocks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:32:10.08398+00:00
-- url     : https://prove2.me/theorems/1616c853-1e47-4803-91bc-44bf01c3ba94
-- title:
--   Lemma 5.4: Algebra type refines every block decomposition
-- statement:
--   Let $\mathcal A\subseteq\mathbb C^{n\times n}$ be a unital star algebra of type $\tau$, meaning an actual unitary decomposition $\bigoplus_i(M_{q_i}(\mathbb C)\otimes I_{k_i})$, with $q_i$ repeated $k_i$ times in $\tau$. For any simultaneous block diagonalization of the whole algebra with block-size multiset $w$,
--
--   $$\tau\text{ refines }w.$$
--
--   Refinement means aggregation of the finer entries into coarser blocks, equivalently multiplication by a zero-one matrix whose columns each sum to one.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 24, Lemma 5.4: Algebra type refines every block decomposition

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

/-- arXiv:2308.00561v1, PDF p.24, Lemma 5.4: Algebra type refines every block decomposition. hasType requires equality of the entire algebra with the Wedderburn block algebra; hasBlocks only requires every algebra element to be block diagonal. Refinement direction is tau -> w. -/
theorem algebraType_refinesBlocks {n : ℕ} (hn : 2 ≤ n) (A : Subalgebra ℂ (Mat n))
    (hstar : starClosed A) (tau w : Multiset ℕ) (ht : hasType A tau) (hb : hasBlocks A w) :
    refines tau w := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
