-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bse_fidelity_monotone
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bse_fidelity_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:43:40.839905+00:00
-- url     : https://prove2.me/theorems/1f00ec8f-366f-4d90-a8a7-525b1a92eddf
-- title:
--   Corollary 7.4: maximum G-BSE fidelity monotonicity
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For a nonzero input Bose projector and a compatible free G-BSE channel, the attained maximum squared input BSE fidelity does not exceed the output maximum. The channel property and input feasibility imply output feasibility.
--
--   $$
--   \max_{\sigma\in\mathrm{BSE}_{U}}F(\rho,\sigma)\le\max_{\tau\in\mathrm{BSE}_{V}}F(\mathcal N(\rho),\tau),\qquad\mathrm{BSE}_{U}\ne\varnothing.
--   $$
--
--   A free BSE channel has a CPTP extension with the same marginal identity and $\mathcal M^\dagger(\Pi_V)\succeq\Pi_U$. $U,V$ refer to the fixed input/output extension data; no covariance is substituted for this inequality.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 36, Corollary 7.4: maximum G-BSE fidelity monotonicity

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

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2BorelSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2BorelSpace

/-- PDF p.36, Corollary 7.4. Source correction: the input comparison set must
be nonempty; rho itself need not be a free state. The output set is then nonempty. -/
theorem bse_fidelity_monotone [Nonempty S] [Nonempty R] [Nonempty R2] [Nonempty S2] (U : G →* Matrix.unitaryGroup (R × S) ℂ)
    (V : G →* Matrix.unitaryGroup (R2 × S2) ℂ)
    (N : Superop S S2) (hN : BSEChannel (fun g => (U g : Mat (R × S)))
      (fun g => (V g : Mat (R2 × S2))) N)
    (hfeasible : ∃ sigma, BSE (fun g => (U g : Mat (R × S))) sigma)
    (rho : Mat S) (hrho : IsDensityMatrix rho) :
    ∃ v w : ℝ, IsGreatest (symmetryFidelityValues rho (BSE (fun g => (U g : Mat (R × S))))) v ∧
      IsGreatest (symmetryFidelityValues (N rho) (BSE (fun g => (V g : Mat (R2 × S2))))) w ∧ v ≤ w := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
