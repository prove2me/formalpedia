-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_separable_bose_extension
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.separable_bose_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:20:55.443019+00:00
-- url     : https://prove2.me/theorems/ee411f60-af1e-474d-85a9-e46d9425eadc
-- title:
--   Explicit Bose extensions of separable states, (93)–(94)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For a finite probability mixture σAB=Σx px |ax⟩⟨ax|⊗|bx⟩⟨bx| of unit product vectors and k≥1, the displayed constructed ω is a density matrix with marginal σAB and Bose support on B copies. Consequently every separable finite-dimensional state is k-Bose extendible and hence k-extendible.
--
--   $$
--   \omega_{AB_1\cdots B_k}=\sum_xp_x|a_x\rangle\langle a_x|\otimes(|b_x\rangle\langle b_x|)^{\otimes k},\quad\operatorname{Tr}_{B_2\cdots B_k}\omega=\sigma_{AB}.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 14, Explicit Bose extensions of separable states, (93)–(94)

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

/-- PDF p.14, (93)–(94): a normalized, Bose-supported extension with the stated
marginal, constructed from the mixture; k = n+1 includes k=1. -/
theorem separable_bose_extension [Nonempty A] [Nonempty B] {X : Type*} [Fintype X]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (a : X → EuclideanSpace ℂ A) (b : X → EuclideanSpace ℂ B)
    (ha : ∀ x, ‖a x‖ = 1) (hb : ∀ x, ‖b x‖ = 1) (n : ℕ) :
    Bose (symmetryControlAverage (kFamily (A := A) (B := B) n)) (separableExtension p a b n) ∧
    traceLeft (separableExtension p a b n) =
      ∑ x, (p x : ℂ) • Matrix.kronecker (pureDensity (a x)) (pureDensity (b x)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
