-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_solutions_measurableIntegralRepresentation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.solutions_measurableIntegralRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:46:43.364186+00:00
-- url     : https://prove2.me/theorems/14140538-e90b-4795-b44d-bf7a50feefb5
-- title:
--   Remark 2.3: measurable integral representation
-- statement:
--   On an interval $I=[0,T]$ with $T\ge0$, or $I=[0,\infty)$, a simplex path $\lambda$ solves (R), respectively (C), if and only if there is a measurable matrix field $A(t)\in\mathcal L$, respectively $A(t)\in\operatorname{conv}\mathcal L$, whose velocity $A(t)\lambda(t)$ is locally integrable and
--
--   $$\lambda(t)=\lambda(0)+\int_0^tA(\tau)\lambda(\tau)\,d\tau\qquad(t\in I).$$
--
--   Here $A=-M$ in the source notation. Both reduced and relaxed representations are retained, with actual Bochner integrability rather than a default integral value.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 7, Remark 2.3: measurable integral representation

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

/-- arXiv:2308.00561v1, PDF p.7, Remark 2.3: measurable integral representation. Both source time domains, I=[0,T] and I=[0,infinity), are included. Interval integrability is part of integralPath, and means local absolute continuity on the infinite horizon. -/
theorem solutions_measurableIntegralRepresentation {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (I : Set ℝ) (hI : (∃ T : ℝ, 0 ≤ T ∧ I = Set.Icc 0 T) ∨ I = Set.Ici 0)
    (path : ℝ → Vec n) :
    (reducedSolution D I path ↔
      (∀ t ∈ I, path t ∈ simplex n) ∧ ∃ A : ℝ → RMat n,
        @Measurable I (RMat n) inferInstance (borel (RMat n)) (fun t : I => A t) ∧
        (∀ t ∈ I, A t ∈ fields D) ∧
        integralPath I path (fun t => A t *ᵥ path t)) ∧
    (relaxedSolution D I path ↔
      (∀ t ∈ I, path t ∈ simplex n) ∧ ∃ A : ℝ → RMat n,
        @Measurable I (RMat n) inferInstance (borel (RMat n)) (fun t : I => A t) ∧
        (∀ t ∈ I, A t ∈ convexHull ℝ (fields D)) ∧
        integralPath I path (fun t => A t *ᵥ path t)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
