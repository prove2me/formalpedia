-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_minimalCollecting_extremalStationarity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.minimalCollecting_extremalStationarity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:42:33.769579+00:00
-- url     : https://prove2.me/theorems/023c4792-3386-4f03-a73f-c5cc391063b0
-- title:
--   Lemma C.12: Minimal collecting supports and extremal stationary states
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, and a complex linear subspace $S$, these are equivalent:
--
--   $$S\text{ minimal nonzero collecting}\quad\Longleftrightarrow\quad\exists\rho\text{ extremal stationary}:\operatorname{supp}\rho=S\quad\Longleftrightarrow\quad\text{a unique stationary density on }S\text{ has full support }S.$$
--
--   Extremality is among all stationary densities; uniqueness is restricted to densities supported in $S$. No global attraction is added.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 33, Lemma C.12: Minimal collecting supports and extremal stationary states

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

/-- arXiv:2308.00561v1, PDF p.33, Lemma C.12: Minimal collecting supports and extremal stationary states. Printed minimal collecting subspace of S is interpreted as an atom of the collecting lattice, per footnote 24. At S=0 every clause is false, since a density has nonzero support. -/
theorem minimalCollecting_extremalStationarity {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (S : Submodule ℂ (Hilbert n)) :
    List.TFAE [minimalCollecting D S,
      (∃ rho : Mat n, extremalStationary D rho ∧ densitySupport rho = S),
      uniqueStationaryOn D S] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
