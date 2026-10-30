-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_invariant_purification
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.invariant_purification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:10:49.189996+00:00
-- url     : https://prove2.me/theorems/64032d58-35a0-4c16-841d-8fb23d49fbbe
-- title:
--   Theorem 2.1: invariant purification characterization
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   ρS has an invariant density extension on R×S iff a unit vector on (R×S)×(R×S) purifies ρS after discarding R,R̂,Ŝ and is fixed by every U(g)⊗conjugate(U(g)); equivalently that vector is fixed by the average of the doubled representation. Both iff clauses are conclusions.
--
--   $$
--   \rho_S\in\mathrm{SymExt}_G\iff\exists|\psi\rangle:\ \|\psi\|=1,\ \operatorname{Tr}_{R\widehat R\widehat S}\psi=\rho_S,\ (U(g)\otimes\overline U(g))|\psi\rangle=|\psi\rangle\quad(\forall g).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 5, Theorem 2.1: invariant purification characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF p.5, Theorem 2.1; p.41 constructs the invariant purification.
Both the pointwise and average fixed-vector characterizations are conclusions. -/
theorem invariant_purification [Nonempty S] [Nonempty R] (U : G → Matrix.unitaryGroup (R × S) ℂ)
    (hU : IsProjectiveUnitaryLift U) (rho : Mat S) (hrho : IsDensityMatrix rho) :
    (SE (fun g => (U g : Mat (R × S))) rho ↔
      ∃ psi : EuclideanSpace ℂ ((R × S) × (R × S)), ‖psi‖ = 1 ∧
        traceLeft (traceRight (pureDensity psi)) = rho ∧
        ∀ g, psi = act (conjugateTensorAction (fun h => (U h : Mat (R × S))) g) psi) ∧
    (∀ psi : EuclideanSpace ℂ ((R × S) × (R × S)),
      (∀ g, psi = act (conjugateTensorAction (fun h => (U h : Mat (R × S))) g) psi) ↔
        psi = act (symmetryControlAverage (conjugateTensorAction (fun h => (U h : Mat (R × S))))) psi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
