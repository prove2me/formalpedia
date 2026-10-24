-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_complement_equivalence
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.complement_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:40:15.787891+00:00
-- url     : https://prove2.me/theorems/a1ae6f23-a739-4b0d-b09d-023f357654b7
-- title:
--   Equation (2), minimal dilations and double complementation
-- statement:
--   Suppose $\Psi$ and $\Psi'$ are complementary to the same finite-dimensional CP map $\Phi$ with nonzero input. There is a rectangular partial isometry $W$ such that, for every input operator $X$,
--
--   $$\Psi'(X)=W\Psi(X)W^*,\qquad\Psi(X)=W^*\Psi'(X)W.$$
--
--   For any two dilations of $\Phi$ whose environments have minimum possible dimension, one can choose $W$ unitary between the environments, with $V'=(I\otimes W)V$ and $V=(I\otimes W^*)V'$. Any complement of $\Psi$ is equivalent to $\Phi$ by the same two-sided output relation. The zero map may have a zero-dimensional minimal environment. This makes complementarity a relation between CP-map equivalence classes.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 2, Equation (2), minimal dilations and double complementation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- Equation (2), PDF p.2: CP-map equivalence, minimum-dimensional dilation
uniqueness, and double complementation. Printed "channels" is read as CP maps. -/
theorem complement_equivalence [Nonempty A]
    (Phi : Superop A B) (Psi : Superop A C) (Psi2 : Superop A D)
    (h : CPComplementary Phi Psi) (h2 : CPComplementary Phi Psi2) :
    Equivalent Psi Psi2 ∧
    (∀ (V : Matrix (B × C) A ℂ) (W : Matrix (B × D) A ℂ),
      MinimalDilation Phi V → MinimalDilation Phi W →
      ∃ J : Matrix D C ℂ, Jᴴ * J = 1 ∧ J * Jᴴ = 1 ∧
        W = ((1 : Matrix B B ℂ) ⊗ₖ J) * V ∧ V = ((1 : Matrix B B ℂ) ⊗ₖ Jᴴ) * W) ∧
    (∀ Phi2 : Superop A D, CPComplementary Psi Phi2 → Equivalent Phi Phi2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
