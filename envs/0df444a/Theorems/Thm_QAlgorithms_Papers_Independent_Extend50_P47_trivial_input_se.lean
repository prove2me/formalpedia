-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_trivial_input_se
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.trivial_input_se
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:39:50.446352+00:00
-- url     : https://prove2.me/theorems/7722a5b7-5d62-40ac-8431-c60a0cc10de1
-- title:
--   Proposition 7.2: trivial-input symmetric-extendible channels
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   A CPTP preparation channel from one-dimensional S which has an invariant-covariant nonsignaling extension yields a SymExt output state. In particular this holds with the completely trivial input reference used by the proof.
--
--   $$
--   \mathcal N(1)\in\mathrm{SymExt}_{V}\qquad(\dim S=1).
--   $$
--
--   A free SE channel has a CPTP covariant extension $\mathcal M:RS\to R'S'$ satisfying $\operatorname{Tr}_{R'}\mathcal M=\mathcal N\operatorname{Tr}_R$ on every operator. $U$ and $V$ denote the fixed input and output extension representations.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 35, Proposition 7.2: trivial-input symmetric-extendible channels

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

/-- PDF p.35, Proposition 7.2. For a fixed nontrivial input reference, its
normalized identity is invariant and supplies the proof's intended input.
The proof's citation to Definition 2.2 is corrected to Definition 2.1. -/
theorem trivial_input_se [Nonempty R] [Nonempty R2] [Nonempty S2] (U : G → Matrix.unitaryGroup (R × Unit) ℂ)
    (V : G → Matrix.unitaryGroup (R2 × S2) ℂ) (hU : IsProjectiveUnitaryLift U) (hV : IsProjectiveUnitaryLift V)
    (N : Superop Unit S2)
    (hN : SEChannel (fun g => (U g : Mat (R × Unit)))
      (fun g => (V g : Mat (R2 × S2))) N) :
    SE (fun g => (V g : Mat (R2 × S2))) (N 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
