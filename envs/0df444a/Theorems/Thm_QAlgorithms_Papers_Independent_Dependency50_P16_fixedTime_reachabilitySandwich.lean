-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_fixedTime_reachabilitySandwich
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.fixedTime_reachabilitySandwich
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:20:47.592844+00:00
-- url     : https://prove2.me/theorems/429c78a7-b70a-4972-930d-5bcbc6b3a48c
-- title:
--   Proposition 4.1: Fixed-time reachable-set sandwich
-- statement:
--   Let $G=-L$ be a GKSL generator, with full fast Hamiltonian controls, on $\mathbb C^n$, $n\ge2$. Let $\rho_0$ be a normalized density and $\lambda_0\in\Delta^{n-1}$ have the same spectrum. For positive time $T$,
--
--   $$\operatorname{reach}_B(\rho_0,T)\subseteq\{U\operatorname{diag}(\lambda)U^*: \lambda\in\operatorname{reach}_R(\lambda_0,T),\ U\in SU(n)\}\subseteq\overline{\operatorname{reach}_B(\rho_0,T)}.$$
--
--   Only the final set is closed. This compares exact full reachability with spectral reachability and arbitrarily fast endpoint rotations.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 13, Proposition 4.1: Fixed-time reachable-set sandwich

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

/-- arXiv:2308.00561v1, PDF p.13, Proposition 4.1: Fixed-time reachable-set sandwich. Correction (trap 30): source introduces T >= 0, but T=0 contradicts the second inclusion for a nontrivial orbit; use T > 0. Same spectrum is expressed equivalently by unitary-orbit membership. Printed U lambda U* means U diag(lambda) U*. -/
theorem fixedTime_reachabilitySandwich {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (C : FullControls n) (rho : Mat n) (hrho : QAlgorithms.IsDensityMatrix rho)
    (x : Vec n) (hx : x ∈ simplex n) (hspec : rho ∈ orbitSaturation {x})
    (T : ℝ) (hT : 0 < T) :
    reachBAt D C rho T ⊆ orbitSaturation (reachRAt D x T) ∧
      orbitSaturation (reachRAt D x T) ⊆ closure (reachBAt D C rho T) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
