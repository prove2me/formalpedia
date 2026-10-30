-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_symmetric_extension_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.symmetric_extension_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:14:33.210353+00:00
-- url     : https://prove2.me/theorems/a77dc3f3-8004-4922-b371-c60681be33b5
-- title:
--   Theorem 3.4: maximum G-symmetric extendible acceptance
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   Algorithm 4 optimal acceptance equals the attained maximum squared fidelity over marginals of U-invariant density extensions on RS. Return registers are R,R̂,Ŝ; retained S is untouched by the prover; the tested average uses U_RS⊗conjugate(U_RS).
--
--   $$
--   p_4^{\rm opt}=\max_{\sigma\in\mathrm{SymExt}_G}F(\rho,\sigma).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 12, Theorem 3.4: maximum G-symmetric extendible acceptance

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

/-- PDF pp.11–12, Theorem 3.4; (74) supplies the maximization omitted in (73). -/
theorem symmetric_extension_fidelity [Nonempty S] [Nonempty R] [Nonempty P] (U : G → Matrix.unitaryGroup (R × S) ℂ)
    (hU : IsProjectiveUnitaryLift U) (rho : Mat S) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (P × S)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho) :
    TestIdentity psi (seTest (fun g => (U g : Mat (R × S)))) rho
      (SE (fun g => (U g : Mat (R × S)))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
