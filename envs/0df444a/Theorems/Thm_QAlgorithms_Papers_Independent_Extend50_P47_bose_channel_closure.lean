-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bose_channel_closure
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bose_channel_closure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:36:21.565501+00:00
-- url     : https://prove2.me/theorems/44e84bbc-7a66-4185-82de-ebaef804be9d
-- title:
--   Proposition 7.1: Bose channel resource-theory closure
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For fixed ordinary input/intermediate/output group representations, identity is Bose free, composition of two Bose-free CPTP maps is Bose free, and a preparation channel from a one-dimensional trivially represented input is Bose free iff its output density is supported by Πout.
--
--   $$
--   \mathrm{id}_A\in\mathcal F,\quad\mathcal M,\mathcal N\in\mathcal F\Rightarrow\mathcal M\circ\mathcal N\in\mathcal F,\quad\mathcal P_\rho\in\mathcal F(\mathbb C\to B)\iff\rho=\Pi_B\rho\Pi_B.
--   $$
--
--   $\mathcal F$ denotes CPTP maps satisfying $\mathcal N^\dagger(\Pi_B)\succeq\Pi_A$; $\mathcal P_\rho(z)=z\rho$ prepares a density from a one-dimensional trivial input representation.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 33, Proposition 7.1: Bose channel resource-theory closure

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

/-- PDF pp.33–34, Proposition 7.1: identity, composition, and the preparation
channel/state identification. The trivial input representation is the constant 1. -/
theorem bose_channel_closure [Nonempty A] [Nonempty B] [Nonempty C] (U : G →* Matrix.unitaryGroup A ℂ)
    (V : G →* Matrix.unitaryGroup B ℂ) (W : G →* Matrix.unitaryGroup C ℂ) :
    BoseChannel (symmetryControlAverage (fun g => (U g : Mat A))) (symmetryControlAverage (fun g => (U g : Mat A)))
      (fun X => X) ∧
    (∀ (N : Superop A B) (M : Superop B C),
      BoseChannel (symmetryControlAverage (fun g => (U g : Mat A))) (symmetryControlAverage (fun g => (V g : Mat B))) N →
      BoseChannel (symmetryControlAverage (fun g => (V g : Mat B))) (symmetryControlAverage (fun g => (W g : Mat C))) M →
      BoseChannel (symmetryControlAverage (fun g => (U g : Mat A))) (symmetryControlAverage (fun g => (W g : Mat C))) (M ∘ N)) ∧
    (∀ rho : Mat B, IsDensityMatrix rho →
      (BoseChannel (1 : Mat Unit) (symmetryControlAverage (fun g => (V g : Mat B))) (densityPreparation rho) ↔
        Bose (symmetryControlAverage (fun g => (V g : Mat B))) rho)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
