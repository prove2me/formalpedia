-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_enclosure_characterization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.enclosure_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:44:35.728988+00:00
-- url     : https://prove2.me/theorems/53a0a85a-97a8-487d-9171-4dcb217cec22
-- title:
--   Lemma C.16: Enclosure characterizations
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, and a complex linear subspace $S$ with orthogonal projection $P$, these are equivalent:
--
--   $$S\text{ and }S^\perp\text{ collecting}\quad\Longleftrightarrow\quad S\text{ invariant under }\operatorname{alg}(I,H_0,V_k,V_k^*)\quad\Longleftrightarrow\quad[P,V_k]=[P,H_0]=0\text{ for every }k.$$
--
--   These define enclosures. The collecting-lattice convention includes zero and the whole space, so all endpoint subspaces are included.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 34, Lemma C.16: Enclosure characterizations

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

/-- arXiv:2308.00561v1, PDF p.34, Lemma C.16: Enclosure characterizations. Convention completion: collecting0 is used to include zero per footnote 23. Printed subset means complex linear subspace; H is the original drift H0. -/
theorem enclosure_characterization {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (S : Submodule ℂ (Hilbert n)) :
    List.TFAE [collecting0 (driftK D) D.jump S ∧ collecting0 (driftK D) D.jump Sᗮ,
      invariant (extendedStarAlgebra D : Set (Mat n)) S,
      enclosure D S] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
