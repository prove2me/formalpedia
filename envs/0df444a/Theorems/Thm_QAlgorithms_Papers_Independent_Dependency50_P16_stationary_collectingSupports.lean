-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_stationary_collectingSupports
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.stationary_collectingSupports
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:41:35.391297+00:00
-- url     : https://prove2.me/theorems/f25bc6be-10c5-4c6f-ac09-72a3a1b4962c
-- title:
--   Lemma C.10: Fixed points and collecting supports
-- statement:
--   For a trace-preserving GKSL generator on $\mathbb C^n$, $n\ge2$,
--
--   $$\rho\text{ stationary density}\Longrightarrow\operatorname{supp}\rho\text{ collecting},$$
--
--   and every nonzero collecting subspace $S$ supports a stationary density $\rho$ with $\operatorname{supp}\rho\subseteq S$. These are both support conclusions, without uniqueness or attraction.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 33, Lemma C.10: Fixed points and collecting supports

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

/-- arXiv:2308.00561v1, PDF p.33, Lemma C.10: Fixed points and collecting supports. Scope correction (traps 19,30): the appendix permits general CP generators, but the collecting-support existence clause needs trace preservation. Restrict to GKSL generators as in the paper standing model: K=-I with no jumps gives G=2 id and no stationary density. Nonzero collecting subspaces are retained. -/
theorem stationary_collectingSupports {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    (∀ rho : Mat n, stationary D rho → collecting (driftK D) D.jump (densitySupport rho)) ∧
    (∀ S : Submodule ℂ (Hilbert n), collecting (driftK D) D.jump S →
      ∃ rho : Mat n, stationary D rho ∧ densitySupport rho ≤ S) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
