-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_flowBarrier_coolingObstruction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.flowBarrier_coolingObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:24:03.412502+00:00
-- url     : https://prove2.me/theorems/65f1bbf1-1ed2-44bd-95af-24414637f4f3
-- title:
--   Corollary 4.6: Flow barrier and eigenvector obstruction to cooling
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, suppose every common jump eigenvector is also a common adjoint-jump eigenvector. There is one constant $C>0$, uniform over all controls and trajectories and bounding inflow by $C$ times outflow, such that every solution $\lambda$ of (C) satisfies
--
--   $$\lambda_1(t)\le\max\left\{\lambda_1(0),\frac C{1+C}\right\}\quad(t\ge0).$$
--
--   Consequently, if $\lambda(0)\ne e_1$ and $t_k\to\infty$ with $\lambda(t_k)\to e_1$, the jumps have a common right eigenvector which is not a common left eigenvector. This gives an obstruction to cooling.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 16, Corollary 4.6: Flow barrier and eigenvector obstruction to cooling

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

/-- arXiv:2308.00561v1, PDF p.16, Corollary 4.6: Flow barrier and eigenvector obstruction to cooling. Both clauses are retained. The family constant precedes every trajectory; the cooling consequence has no obstruction hypothesis. Sequences use nonnegative times tending to infinity. -/
theorem flowBarrier_coolingObstruction {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) (i0 : Fin n) (hi0 : i0.val = 0) :
    (eigenvectorObstruction D.jump → ∃ C : ℝ, 0 < C ∧
      (∀ U : Mat n, specialUnitary U → inflow D.jump 1 U ≤ C * outflow D.jump 1 U) ∧
      ∀ path, relaxedSolution D (Set.Ici 0) path →
        ∀ t ≥ 0, path t i0 ≤ max (path 0 i0) (C / (1 + C))) ∧
    (∀ path, relaxedSolution D (Set.Ici 0) path → path 0 ≠ vertex i0 →
      (∃ times : ℕ → ℝ, (∀ k, 0 ≤ times k) ∧ Tendsto times atTop atTop ∧
        Tendsto (fun k => path (times k)) atTop (nhds (vertex i0))) →
      ∃ psi, commonEigenvector D.jump psi ∧
        ¬commonEigenvector (fun k => (D.jump k)ᴴ) psi) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
