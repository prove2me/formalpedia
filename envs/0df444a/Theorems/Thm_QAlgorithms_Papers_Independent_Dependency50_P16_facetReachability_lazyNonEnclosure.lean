-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_facetReachability_lazyNonEnclosure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.facetReachability_lazyNonEnclosure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:28:01.915601+00:00
-- url     : https://prove2.me/theorems/b30a6752-632f-4628-b3cb-db665b208d38
-- title:
--   Corollary 4.17: Necessary lazy-subspace condition for reaching a facet
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, if a facet $F$ of the simplex is directly reachable, then
--
--   $$\exists S\subseteq\mathbb C^n:\quad\dim S=n-1,\quad S\text{ lazy and not an enclosure}.$$
--
--   A facet has affine dimension $n-2$. This is a necessary condition, including the vertex facets when $n=2$.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 20, Corollary 4.17: Necessary lazy-subspace condition for reaching a facet

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

/-- arXiv:2308.00561v1, PDF p.20, Corollary 4.17: Necessary lazy-subspace condition for reaching a facet.  -/
theorem facetReachability_lazyNonEnclosure {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (F : Face n) (hfacet : F.support.card = n - 1) (hF : directlyReachable D F) :
    ∃ S : Submodule ℂ (Hilbert n), lazy D.jump S ∧ Module.finrank ℂ S = n - 1 ∧
      ¬enclosure D S := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
