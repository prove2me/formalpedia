-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_sourceReplacement
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.sourceReplacement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:39:32.506925+00:00
-- url     : https://prove2.me/theorems/868be5e4-bb16-4924-84ce-e069855e4e91
-- title:
--   II.B.2: prepare-and-measure / entanglement-based source replacement, Eq.(4)
-- statement:
--   Let $S$ be a finite nonempty set, $d=|S|$, and let $\psi_s$ be unit vectors in an arbitrary complex Hilbert signal space $H$. In $\mathbb C^S\otimes H$, construct the vector with orthogonal-label components $\Phi_s=\psi_s/\sqrt d$. It has unit norm. Measuring the label gives each $s$ with probability $1/d$, and the conditional normalized signal is $\psi_s$:
--
--   $$\rho_{H,s}=d^{-1}|\psi_s\rangle\langle\psi_s|,\qquad \rho_H=d^{-1}\sum_s|\psi_s\rangle\langle\psi_s|.$$
--
--   The same equality holds after any subsequent linear transformation of signal operators, including a channel with joint Bob–Eve output and any following measurement. Thus the labelled output states of the two source realizations agree. No finite cutoff is imposed on $H$; the finite direct sum is the canonical label-register tensor representation. This is source equivalence in the ordinary trusted-device model.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 8, II.B.2: prepare-and-measure / entanglement-based source replacement, Eq.(4)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(4), PDF p.8: uniform source replacement and preservation under every
linear subsequent transformation, including channels with joint Bob–Eve output. -/
theorem sourceReplacement {S H V : Type*} [Fintype S] [Nonempty S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommMonoid V] [Module ℂ V] (psi : S → H) (hpsi : ∀ s, ‖psi s‖ = 1)
    (L : (H →L[ℂ] H) →ₗ[ℂ] V) :
    ‖sourceReplacementVector psi‖ = 1 ∧
    (∀ s, ‖sourceReplacementVector psi s‖^2 = (Fintype.card S : ℝ)⁻¹ ∧
      ((Real.sqrt (Fintype.card S : ℝ)) : ℂ) • sourceReplacementVector psi s = psi s ∧
      replacementBlock psi s = ((Fintype.card S : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ (psi s) (psi s) ∧
      L (replacementBlock psi s) = ((Fintype.card S : ℂ)⁻¹) • L (InnerProductSpace.rankOne ℂ (psi s) (psi s))) ∧
    replacementReduction psi = ((Fintype.card S : ℂ)⁻¹) •
      ∑ s, InnerProductSpace.rankOne ℂ (psi s) (psi s) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
