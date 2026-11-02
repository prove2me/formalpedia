-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_controlledUnitary_content_cost
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.controlledUnitary_content_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:09:38.407566+00:00
-- url     : https://prove2.me/theorems/f77033f1-7c9d-453c-8fdc-de82500b35ed
-- title:
--   Controlled-unitary content from folded eigenphases and its cost
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. Let $W$ be any one-qubit unitary and $\mathrm{ctrl}\text{-}W=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes W$. There exists a scalar $z$ of modulus one such that $zW$ has eigenvalues $e^{2ib},e^{-2ib}$ for some $0\le b\le\pi/2$. For every such choice let $c=\min\{b,\pi/2-b\}$. Assuming $\alpha_1>0$,
--
--   $$\beta(\mathrm{ctrl}\text{-}W)=(c,0,0),\qquad C_H(\mathrm{ctrl}\text{-}W)=\frac{c}{\alpha_1}.$$
--
--   The scalar phase of $W$ induces a free phase gate on the control. Folding the half-angle removes the branch ambiguity in the interaction content.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 7, III.D.1 and Appendix A: controlled-U content and cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF pp.7,13, III.D.1 and Appendix A: after a free determinant phase, the eigenvalues
are exp(±2ib), 0≤b≤pi/2. The content coordinate is min(b,pi/2-b). -/
theorem controlledUnitary_content_cost (W : OneGate) (H : TwoMatrix) (a : Triple)
    (hH : HasCanonicalHamiltonian H a) (ha : 0 < a 0) :
    (∃ b : ℝ, ControlPhase (W : OneMatrix) b) ∧
    ∀ b : ℝ, ControlPhase (W : OneMatrix) b →
      HasContent (controlled (W : OneMatrix)) (controlledContent b) ∧
      interactionCost H (controlled (W : OneMatrix)) =
        ENNReal.ofReal (min b (Real.pi / 2 - b) / a 0) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
