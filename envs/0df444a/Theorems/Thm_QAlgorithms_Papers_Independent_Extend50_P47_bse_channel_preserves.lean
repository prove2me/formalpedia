-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bse_channel_preserves
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bse_channel_preserves
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:42:57.167989+00:00
-- url     : https://prove2.me/theorems/65863f2f-9883-49eb-be02-9370fe893a35
-- title:
--   Proposition 7.5: Bose-extension preservation
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   A CPTP N with nonsignaling channel extension M satisfying M†Πout≥Πin takes every state with a Bose-supported input extension to a state with a Bose-supported output extension.
--
--   $$
--   \rho\in\mathrm{BSE}_{U}\Rightarrow\mathcal N(\rho)\in\mathrm{BSE}_{V}.
--   $$
--
--   A free BSE channel has a CPTP extension with the same marginal identity and $\mathcal M^\dagger(\Pi_V)\succeq\Pi_U$. $U,V$ refer to the fixed input/output extension data; no covariance is substituted for this inequality.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 36, Proposition 7.5: Bose-extension preservation

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

/-- PDF pp.36,44–45, Proposition 7.5: preserve Bose extensions via the adjoint
inequality of Definition 7.3. An input Bose state already witnesses feasibility. -/
theorem bse_channel_preserves [Nonempty S] [Nonempty R] [Nonempty R2] [Nonempty S2] (U : G →* Matrix.unitaryGroup (R × S) ℂ)
    (V : G →* Matrix.unitaryGroup (R2 × S2) ℂ)
    (N : Superop S S2) (hN : BSEChannel (fun g => (U g : Mat (R × S)))
      (fun g => (V g : Mat (R2 × S2))) N)
    (rho : Mat S) (hrho : BSE (fun g => (U g : Mat (R × S))) rho) :
    BSE (fun g => (V g : Mat (R2 × S2))) (N rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
