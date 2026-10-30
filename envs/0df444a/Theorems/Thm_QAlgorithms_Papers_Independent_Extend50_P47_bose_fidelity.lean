-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bose_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bose_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:11:37.665715+00:00
-- url     : https://prove2.me/theorems/f71d375a-63ae-4503-a1ad-4770eaab2a67
-- title:
--   Theorem 3.1: maximum G-Bose symmetric fidelity
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For nonzero ΠU, Algorithm 1 accepts with probability Tr(ΠUρ), which equals an attained maximum of F(ρ,σ) over density matrices satisfying σ=ΠUσΠU. In the excluded case, ΠU=0 gives acceptance 0 and no Bose-symmetric states, so the printed maximum does not exist in that case.
--
--   $$
--   p_{\rm acc}=\operatorname{Tr}(\Pi\rho)=\max_{\sigma\in\mathrm{B\!\text{-}Sym}_G}F(\rho,\sigma)\quad(\Pi\ne0).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 7, Theorem 3.1: maximum G-Bose symmetric fidelity

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

/-- PDF p.7, Theorem 3.1. Source correction: a Bose maximum requires a nonzero
projector; the zero-projector case has zero acceptance and no comparison density. -/
theorem bose_fidelity [Nonempty S] (U : G →* Matrix.unitaryGroup S ℂ)
    (rho : Mat S) (hrho : IsDensityMatrix rho) :
    controlReturnProbability (symmetryControlAverage (fun g => (U g : Mat S))) rho =
      effectProb (symmetryControlAverage (fun g => (U g : Mat S))) rho ∧
    (symmetryControlAverage (fun g => (U g : Mat S)) ≠ 0 →
      IsGreatest (symmetryFidelityValues rho (Bose (symmetryControlAverage (fun g => (U g : Mat S)))))
        (effectProb (symmetryControlAverage (fun g => (U g : Mat S))) rho)) ∧
    (symmetryControlAverage (fun g => (U g : Mat S)) = 0 →
      controlReturnProbability (symmetryControlAverage (fun g => (U g : Mat S))) rho = 0 ∧
      ¬ ∃ sigma, Bose (symmetryControlAverage (fun g => (U g : Mat S))) sigma) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
