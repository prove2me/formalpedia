-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_k_channel_specialization
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.k_channel_specialization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:44:19.536782+00:00
-- url     : https://prove2.me/theorems/af320422-1d80-4b56-8587-e61d10d45a1f
-- title:
--   Example 7.1: k-extendible channels as SE channels
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For k≥1 and nonzero finite A,B,A′,B′, the channel extension and permutation covariance conditions (244)–(245) are exactly Definition 7.2 under S=AB1,R=B2···Bk,S′=A′B′1,R′=B′2···B′k and U=IA⊗W,V=IA′⊗W′.
--
--   $$
--   k\text{-extendible channels}=\mathrm{SEChan}_{I_A\otimes W,I_C\otimes W'},\quad G=S_k.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 35, Example 7.1: k-extendible channels as SE channels

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

/-- PDF p.35, Example 7.1: the source's k-extendible-channel model is a
specialization of the general framework, with k=n+1. -/
theorem k_channel_specialization [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] (n : ℕ) (N : Superop (A × B) (C × D))
    : KChannel n N ↔
    SEChannel (kFamily (A := A) (B := B) n) (kFamily (A := C) (B := D) n) N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
