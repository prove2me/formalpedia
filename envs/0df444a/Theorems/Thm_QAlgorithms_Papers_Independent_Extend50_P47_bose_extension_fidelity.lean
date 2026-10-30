-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bose_extension_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bose_extension_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:13:35.542211+00:00
-- url     : https://prove2.me/theorems/6621fc1a-dacf-49be-9f04-d9106ebad07b
-- title:
--   Theorem 3.3: maximum G-BSE acceptance
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register. The input includes a unit purification of $\rho_S$. The prover acts only on its purifying register, with arbitrary ancillas and a retained private environment, and returns the prescribed registers. It never acts on retained $S$. All maxima mentioned below are attained.
--
--   For nonzero ΠURS, Algorithm 3 optimal acceptance is the attained maximum squared fidelity with marginals TrR ω of density extensions ω supported by ΠURS. In addition, ΠURS=0 implies optimal acceptance zero and an empty BSE set.
--
--   $$
--   p_3^{\rm opt}=\max_{\sigma\in\mathrm{BSE}_G}F(\rho,\sigma)\quad(\Pi_{RS}\ne0).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 11, Theorem 3.3: maximum G-BSE acceptance

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

/-- PDF pp.10–11, Theorem 3.3. Source correction: include the feasible Bose
maximum and separately the excluded zero-projector operational case. -/
theorem bose_extension_fidelity [Nonempty S] [Nonempty R] [Nonempty P] (U : G →* Matrix.unitaryGroup (R × S) ℂ)
    (rho : Mat S) (hrho : IsDensityMatrix rho) (psi : EuclideanSpace ℂ (P × S))
    (hpsi : ‖psi‖ = 1) (hpur : traceLeft (pureDensity psi) = rho) :
    (symmetryControlAverage (fun g => (U g : Mat (R × S))) ≠ 0 →
      TestIdentity psi (symmetryControlAverage (fun g => (U g : Mat (R × S)))) rho
        (BSE (fun g => (U g : Mat (R × S))))) ∧
    (symmetryControlAverage (fun g => (U g : Mat (R × S))) = 0 →
      IsGreatest (proverValues psi (symmetryControlAverage (fun g => (U g : Mat (R × S))))) 0 ∧
        ¬ ∃ sigma, BSE (fun g => (U g : Mat (R × S))) sigma) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
