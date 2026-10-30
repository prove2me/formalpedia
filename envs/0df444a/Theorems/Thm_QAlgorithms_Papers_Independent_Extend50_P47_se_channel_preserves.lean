-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_se_channel_preserves
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.se_channel_preserves
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:40:36.826256+00:00
-- url     : https://prove2.me/theorems/1bac6187-3129-4883-ba2a-f41f513ace9e
-- title:
--   Proposition 7.3: invariant-extension preservation
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For CPTP N with a CPTP covariant channel extension M on RS→R′S′ satisfying the marginal identity, every state with an invariant RS extension is mapped to a state with an invariant R′S′ extension.
--
--   $$
--   \rho\in\mathrm{SymExt}_{U}\Rightarrow\mathcal N(\rho)\in\mathrm{SymExt}_{V}.
--   $$
--
--   A free SE channel has a CPTP covariant extension $\mathcal M:RS\to R'S'$ satisfying $\operatorname{Tr}_{R'}\mathcal M=\mathcal N\operatorname{Tr}_R$ on every operator. $U$ and $V$ denote the fixed input and output extension representations.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 35, Proposition 7.3: invariant-extension preservation

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

/-- PDF p.35, Proposition 7.3: compatible fixed representations and references. -/
theorem se_channel_preserves [Nonempty S] [Nonempty R] [Nonempty R2] [Nonempty S2] (U : G → Matrix.unitaryGroup (R × S) ℂ)
    (V : G → Matrix.unitaryGroup (R2 × S2) ℂ) (hU : IsProjectiveUnitaryLift U) (hV : IsProjectiveUnitaryLift V)
    (N : Superop S S2) (hN : SEChannel (fun g => (U g : Mat (R × S)))
      (fun g => (V g : Mat (R2 × S2))) N)
    (rho : Mat S) (hrho : SE (fun g => (U g : Mat (R × S))) rho) :
    SE (fun g => (V g : Mat (R2 × S2))) (N rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
