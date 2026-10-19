-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_minimalAsymptotic_characterization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.minimalAsymptotic_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:43:09.691988+00:00
-- url     : https://prove2.me/theorems/d6af7f98-8366-42a5-ad92-abdc6b79ef1c
-- title:
--   Lemma C.13: Minimal asymptotic subspace
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, a subspace $S$ is the minimal asymptotic subspace if and only if
--
--   $$S=\operatorname{span}\{\operatorname{supp}\rho:\rho\text{ a stationary density}\},$$
--
--   and if and only if it is the span of all minimal collecting subspaces. The minimal asymptotic subspace is the orthogonal complement of the maximal decaying subspace. Fixed points here are normalized densities, and invariant subspaces in the final clause refer to the extended relaxation algebra.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 33, Lemma C.13: Minimal asymptotic subspace

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

/-- arXiv:2308.00561v1, PDF p.33, Lemma C.13: Minimal asymptotic subspace. The proof invokes C.12, fixing invariant as collecting, not merely lazy. Submodule suprema compute spans and have no real-supremum junk values. -/
theorem minimalAsymptotic_characterization {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (S : Submodule ℂ (Hilbert n)) :
    List.TFAE [S = minimalAsymptotic D,
      S = sSup {T : Submodule ℂ (Hilbert n) | ∃ rho : Mat n, stationary D rho ∧ T = densitySupport rho},
      S = sSup {T : Submodule ℂ (Hilbert n) | minimalCollecting D T}] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
