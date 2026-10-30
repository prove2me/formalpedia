-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_bose_channel_converse
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.bose_channel_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:38:38.480749+00:00
-- url     : https://prove2.me/theorems/bd0e89ed-5817-4fdb-8620-b682533d55fb
-- title:
--   Converse monotonicity characterization, (231)–(232)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For a fixed CPTP N, N†ΠB≥ΠA iff for every density ρ, Tr(ΠBNρ)≥Tr(ΠAρ).
--
--   $$
--   \mathcal N^\dagger(\Pi_B)\succeq\Pi_A\iff\operatorname{Tr}(\Pi_B\mathcal N(\rho))\ge\operatorname{Tr}(\Pi_A\rho)\quad\text{for every density }\rho.
--   $$
--
--   $\mathcal N$ is one fixed CPTP map. Its adjoint is the Hilbert–Schmidt adjoint, and $\succeq$ denotes the positive-semidefinite order.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 34, Converse monotonicity characterization, (231)–(232)

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

/-- PDF p.34, (231)–(232): the converse requires monotonicity for every input density. -/
theorem bose_channel_converse [Nonempty A] [Nonempty B] (U : G →* Matrix.unitaryGroup A ℂ)
    (V : G →* Matrix.unitaryGroup B ℂ) (N : Superop A B) (hN : IsChannel N) :
    BoseChannel (symmetryControlAverage (fun g => (U g : Mat A))) (symmetryControlAverage (fun g => (V g : Mat B))) N ↔
      ∀ rho, IsDensityMatrix rho → effectProb (symmetryControlAverage (fun g => (U g : Mat A))) rho ≤
        effectProb (symmetryControlAverage (fun g => (V g : Mat B))) (N rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
