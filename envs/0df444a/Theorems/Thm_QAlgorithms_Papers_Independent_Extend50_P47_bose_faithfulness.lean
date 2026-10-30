-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bose_faithfulness
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bose_faithfulness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:15:13.735712+00:00
-- url     : https://prove2.me/theorems/43923372-7331-4a1f-a637-fa23665df1df
-- title:
--   Algorithm 1 faithfulness, equations (36)–(37)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   Algorithm 1 probability is Tr(ΠUρ) and equals one iff ρ=ΠUρΠU; for a unit pure input this is equivalent to ΠUψ=ψ and U(g)ψ=ψ for every g.
--
--   $$
--   p_{\rm acc}=1\iff\rho=\Pi\rho\Pi,\qquad \Pi|\psi\rangle=|\psi\rangle\iff U(g)|\psi\rangle=|\psi\rangle\ (\forall g).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 6, Algorithm 1 faithfulness, equations (36)–(37)

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

/-- PDF pp.6–7, (36)–(37): acceptance one, including the zero-projector case. -/
theorem bose_faithfulness [Nonempty S] (U : G →* Matrix.unitaryGroup S ℂ)
    (rho : Mat S) (hrho : IsDensityMatrix rho) :
    (controlReturnProbability (symmetryControlAverage (fun g => (U g : Mat S))) rho = 1 ↔
      Bose (symmetryControlAverage (fun g => (U g : Mat S))) rho) ∧
    (∀ psi : EuclideanSpace ℂ S, ‖psi‖ = 1 →
      (act (symmetryControlAverage (fun g => (U g : Mat S))) psi = psi ↔
        ∀ g, act (U g : Mat S) psi = psi)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
