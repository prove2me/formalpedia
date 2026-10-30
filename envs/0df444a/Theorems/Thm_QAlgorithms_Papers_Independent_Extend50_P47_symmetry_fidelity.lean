-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_symmetry_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.symmetry_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:12:42.567913+00:00
-- url     : https://prove2.me/theorems/edb96ef6-c3ca-4b1c-bc4f-8b3c0937ae50
-- title:
--   Paper seed / Theorem 3.2: optimal G-symmetry acceptance
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   For every density matrix ρ and any supplied purification, the maximum acceptance of the concrete two-message Algorithm 2 equals an attained maximum of F(ρ,σ) over all density matrices invariant under conjugation by U(g), for every g. The verifier projector is |G|⁻¹Σg U(g)⊗conjugate(U(g)).
--
--   $$
--   p_2^{\rm opt}=\max_{\sigma\in\mathrm{Sym}_G}F(\rho,\sigma).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 9, Paper seed / Theorem 3.2: optimal G-symmetry acceptance

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

/-- PDF pp.8–9, Theorem 3.2 / paper seed; exact semantics of Algorithm 2. -/
theorem symmetry_fidelity [Nonempty S] [Nonempty P] (U : G → Matrix.unitaryGroup S ℂ) (hU : IsProjectiveUnitaryLift U)
    (rho : Mat S) (hrho : IsDensityMatrix rho) (psi : EuclideanSpace ℂ (P × S))
    (hpsi : ‖psi‖ = 1) (hpur : traceLeft (pureDensity psi) = rho) :
    TestIdentity psi (symTest (fun g => (U g : Mat S))) rho
      (Sym (fun g => (U g : Mat S))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
