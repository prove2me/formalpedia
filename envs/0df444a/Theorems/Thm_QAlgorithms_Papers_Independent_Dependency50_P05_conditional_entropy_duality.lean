-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_conditional_entropy_duality
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.conditional_entropy_duality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:58:02.683913+00:00
-- url     : https://prove2.me/theorems/1d752638-a8b2-4c88-81f3-afa1b1f2c923
-- title:
--   Attained entropy primal/dual and Bell-overlap formulas
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\Omega^{AB}$ be a channel and $\omega=J_\Omega/(d_{A_0}d_{B_0})$. Define $h=H_{\min}^{\rm ext}(B|A)_\Omega$ by the primal optimization of Definition 4: minimize $\operatorname{Tr}\gamma$ subject to $\gamma^{AB_0}\otimes I^{B_1}\ge\omega$ and $\gamma^{A_0B_0}=u^{A_0}\otimes\gamma^{B_0}$, then take minus its base-two logarithm. The minimum and the following maxima are attained:
--   $$2^{-h}=d_{A_0}\max_{\alpha}\operatorname{Tr}(\alpha\omega),\qquad d_{B_0}2^{-h}=\max_{\Theta\in S^{AB}}\operatorname{Tr}(J_\Theta J_\Omega).$$
--   The first maximum is over positive $\alpha$ satisfying $\alpha^{AB_0}=\alpha^{A_0B_0}\otimes u^{A_1}$ and $\alpha^{A_1B_0}=I$. Equivalently, the last value is the maximum Bell-output overlap obtained by applying a superchannel to $A$ and the identity to $B$, feeding an unnormalized Bell projector at the two $B_0$ inputs and testing an unnormalized Bell projector at the two $B_1$ outputs, as in Eq.(66). The channel inner product in Eq.(65) is the same Choi trace. This is an equality of optima, not an assumed definition of entropy.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 13, Sec. IV-A, Eqs.(63)–(66); Appendix A-A

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.13–14,22, Eqs.(63)–(66): attained primal/dual support
value and Bell-overlap operational form. The essential INPUT factor d_B0 is retained. -/
theorem conditional_entropy_duality (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B))
    (hW : BipartiteChannel A B W) :
    (∃ G : Mat (ChoiRegister A × In B), EntropyFeasible A B W G ∧
      (G.trace.re : EReal) = entropyPower (extendedConditional A B W) ∧
      ∀ H : Mat (ChoiRegister A × In B), EntropyFeasible A B W H → G.trace.re ≤ H.trace.re) ∧
    (∃ T : Supermap A B, IsSuperchannel T ∧ StandardMarginals T ∧
      entropyPower (extendedConditional A B W) =
        ((A.input : ℝ) * (superChoi T * jointInputNormalizedChoi A B W).trace.re : EReal) ∧
      (B.input : EReal) * entropyPower (extendedConditional A B W) =
        ((superChoi T * W).trace.re : EReal) ∧
      ∀ S : Supermap A B, IsSuperchannel S →
        ((superChoi S * W).trace.re : EReal) ≤
          (B.input : EReal) * entropyPower (extendedConditional A B W)) ∧
    (∃ T : Supermap A B, IsSuperchannel T ∧
      (jointBellOverlap B (localApply T B W) : EReal) =
        (B.input : EReal) * entropyPower (extendedConditional A B W) ∧
      ∀ S : Supermap A B, IsSuperchannel S →
        (jointBellOverlap B (localApply S B W) : EReal) ≤
          (B.input : EReal) * entropyPower (extendedConditional A B W)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
