-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_fully_trivial_input_bse
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.fully_trivial_input_bse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:42:10.698695+00:00
-- url     : https://prove2.me/theorems/5c327968-a61b-486b-8f0c-8396dcf8e1a6
-- title:
--   Proof-intended Proposition 7.4 with a fully trivial input
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For a preparation from the completely trivial input RS with representation g↦1, existence of a CPTP channel extension satisfying M†Πout≥1 is equivalent to the prepared state having a Bose-supported output extension.
--
--   $$
--   \mathcal N(1)\in\mathrm{BSE}_{V}\quad(\dim R=\dim S=1,\ U(g)=1),\qquad\mathcal P_\rho\in\mathrm{BSEChan}_{1,V}\iff\rho\in\mathrm{BSE}_{V}.
--   $$
--
--   A free BSE channel has a CPTP extension with the same marginal identity and $\mathcal M^\dagger(\Pi_V)\succeq\Pi_U$. $U,V$ refer to the fixed input/output extension data; no covariance is substituted for this inequality.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 36, Proof-intended Proposition 7.4 with a fully trivial input

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

/-- PDF p.36, proof-intended Proposition 7.4. Source correction: the entire
input RS has dimension one and the trivial representation, including R. The
literal fixed-reference assertion is separately deferred. -/
theorem fully_trivial_input_bse [Nonempty R2] [Nonempty S2] (V : G →* Matrix.unitaryGroup (R2 × S2) ℂ)
    (N : Superop Unit S2)
    (hN : BSEChannel (fun _ : G => (1 : Mat (Unit × Unit)))
      (fun g => (V g : Mat (R2 × S2))) N) :
    BSE (fun g => (V g : Mat (R2 × S2))) (N 1) ∧
    (∀ rho : Mat S2, IsDensityMatrix rho →
      (BSEChannel (fun _ : G => (1 : Mat (Unit × Unit)))
        (fun g => (V g : Mat (R2 × S2))) (densityPreparation rho) ↔
        BSE (fun g => (V g : Mat (R2 × S2))) rho)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
