-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_cooling_constantHamiltonianAttraction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.cooling_constantHamiltonianAttraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:24:43.125237+00:00
-- url     : https://prove2.me/theorems/cfc7492d-8eb2-42ef-b691-118c860ac956
-- title:
--   Theorem 4.7: Asymptotic cooling equals constant-Hamiltonian pure-state global attraction
-- statement:
--   For a GKSL generator $G=-L$ on $\mathbb C^n$, $n\ge2$, the following four statements are equivalent:
--
--   1. Every jump representation has a common right eigenvector which is not a common left eigenvector.
--   2. There is a time-independent Hermitian $H$ such that $G-i[H,\cdot]$ has a pure attractive fixed density.
--   3. From every initial simplex state there is a solution of (R) converging to $e_1$.
--   4. For some $\lambda\in\Delta^{n-1}\setminus\{e_1\}$,
--
--   $$e_1\in\overline{\operatorname{reach}_R(\lambda)}.$$
--
--   Attractive means every initial density converges to the fixed point, which makes it unique. The attracting pure state is existential, not a prescribed common eigenvector.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 17, Theorem 4.7: Asymptotic cooling equals constant-Hamiltonian pure-state global attraction

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

/-- arXiv:2308.00561v1, PDF p.17, Theorem 4.7: Asymptotic cooling equals constant-Hamiltonian pure-state global attraction. PDF p.17 and footnote 13: all four clauses, closure in (iv), one constant H before all initial densities, and a trajectory allowed to depend on the initial spectrum. No target-specific GAS interface is inferred. -/
theorem cooling_constantHamiltonianAttraction {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (i0 : Fin n) (hi0 : i0.val = 0) :
    List.TFAE [
      everyRepresentation D (fun E => ∃ psi, commonEigenvector E.jump psi ∧
        ¬commonEigenvector (fun k => (E.jump k)ᴴ) psi),
      (∃ (H : Mat n) (hH : H.IsHermitian) (psi : Hilbert n), ‖psi‖ = 1 ∧
        attractive (controlledData D H hH) (QAlgorithms.pureDensity psi)),
      coolable D i0,
      (∃ x ∈ simplex n, x ≠ vertex i0 ∧ vertex i0 ∈ closure (reachR D x))] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
