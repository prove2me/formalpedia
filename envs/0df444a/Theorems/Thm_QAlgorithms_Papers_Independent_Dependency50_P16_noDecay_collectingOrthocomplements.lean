-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_noDecay_collectingOrthocomplements
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.noDecay_collectingOrthocomplements
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:43:47.103275+00:00
-- url     : https://prove2.me/theorems/76884188-ac58-4f5e-a305-6cb79959cacb
-- title:
--   Lemma C.15: Absence of decay and orthocomplemented collecting lattice
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$,
--
--   $$\text{the minimal asymptotic subspace is }\mathbb C^n\quad\Longleftrightarrow\quad\operatorname{Lat}(\mathcal V^+)\text{ is orthocomplemented and }\mathcal V^+\text{ is a star algebra}.$$
--
--   The lattice includes zero, and orthocomplemented specifically means closure under the Hilbert-space orthogonal complement. This retains the star-algebra conclusion of the source.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 34, Lemma C.15: Absence of decay and orthocomplemented collecting lattice

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

/-- arXiv:2308.00561v1, PDF p.34, Lemma C.15: Absence of decay and orthocomplemented collecting lattice.  -/
theorem noDecay_collectingOrthocomplements {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    minimalAsymptotic D = ⊤ ↔
      (∀ S : Submodule ℂ (Hilbert n), collecting0 (driftK D) D.jump S →
        collecting0 (driftK D) D.jump Sᗮ) ∧ starClosed (extendedAlgebra (driftK D) D.jump) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
