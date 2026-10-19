-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_threeDimensions_directReachabilityConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.threeDimensions_directReachabilityConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:28:34.900849+00:00
-- url     : https://prove2.me/theorems/58264d55-db21-43d0-ae1c-de740d871ea6
-- title:
--   Corollary 4.18: Converse in dimension three
-- statement:
--   For a GKSL generator on $\mathbb C^3$, let $F$ be a proper nonempty simplex face. If $F$ is directly reachable, then
--
--   $$\exists S\subseteq\mathbb C^3:\quad\dim S=\dim F+1,\quad S\text{ lazy and not an enclosure}.$$
--
--   Thus the converse of Corollary 4.13 holds in dimension three, for both vertices and edges. The unconditional forward implication of that corollary is not included.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 20, Corollary 4.18: Converse in dimension three

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

/-- arXiv:2308.00561v1, PDF p.20, Corollary 4.18: Converse in dimension three.  -/
theorem threeDimensions_directReachabilityConverse (D : LindbladData 3) (F : Face 3)
    (hproper : F.support.card < 3) (hF : directlyReachable D F) :
    ∃ S : Submodule ℂ (Hilbert 3), lazy D.jump S ∧ Module.finrank ℂ S = F.support.card ∧
      ¬enclosure D S := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
