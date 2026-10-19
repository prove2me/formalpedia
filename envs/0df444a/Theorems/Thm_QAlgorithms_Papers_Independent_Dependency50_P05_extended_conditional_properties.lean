-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_extended_conditional_properties
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.extended_conditional_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:58:55.947494+00:00
-- url     : https://prove2.me/theorems/bbb422c2-44b4-4132-bd1d-bac70565b59c
-- title:
--   All six properties of extended conditional min-entropy
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. For a bipartite channel $\Omega^{AB}$ let $\omega=J_\Omega/(d_{A_0}d_{B_0})$ and use the primal extended conditional min-entropy of Definition 4, with base-two logarithms. The following six properties hold:
--
--   1. If $\Omega$ replaces every input by a fixed density matrix $\rho^{A_1B_1}$, then $H_{\min}^{\rm ext}(B|A)_\Omega=H_{\min}(B_1|A_1)_\rho$.
--   2. For any local channels $\Psi^A,\Phi^B$ with $\Omega=\Psi\otimes\Phi$, $H_{\min}^{\rm ext}(B|A)_\Omega=H_{\min}^{\rm ext}(B)_\Phi$.
--   3. For every second bipartite channel $\Gamma^{A'B'}$, entropy adds under tensor product.
--   4. Every superchannel $\Theta:A\to C$ satisfies $H_{\min}^{\rm ext}(B|A)_\Omega\le H_{\min}^{\rm ext}(B|C)_{(\Theta\otimes1^B)[\Omega]}$.
--   5. For every tripartite channel $Z^{ABC}$ and every density matrix $\tau^{C_0}$, let $Z_\tau^{AB}(X)=\operatorname{Tr}_{C_1}Z(X\otimes\tau)$. Then $H_{\min}^{\rm ext}(B|AC)_Z\le H_{\min}^{\rm ext}(B|A)_{Z_\tau}$.
--   6. The bounds are
--   $$H_{\min}(AB_1|B_0)_\omega-\log_2(d_{A_0}d_{A_1})\ \le\ H_{\min}^{\rm ext}(B|A)_\Omega\ \le\ H_{\min}(B_1|A_1)_\omega.$$
--
--   In clause 3 the full formula is $H_{\min}^{\rm ext}(BB'|AA')_{\Omega\otimes\Gamma}=H_{\min}^{\rm ext}(B|A)_\Omega+H_{\min}^{\rm ext}(B'|A')_\Gamma$. In the lower bound $A=A_0A_1$. All state conditional min-entropies use the indicated ordinary marginals of $\omega$. These properties extend state entropy behavior to dynamical conditioning.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 14, Theorem 5, Eqs.(67)–(71)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.14–15, Theorem 5: all SIX properties in one headline.
Conditioning quantifies the inserted C0 state, as required by Remark 4. -/
theorem extended_conditional_properties (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B))
    (hW : BipartiteChannel A B W) :
    (∀ R : Mat (Out A × Out B), QAlgorithms.IsDensityMatrix R → W = replacementChoi A B R →
      extendedConditional A B W = stateConditional R) ∧
    (∀ (X : Mat (ChoiRegister A)) (Y : Mat (ChoiRegister B)), ChannelChoi X → ChannelChoi Y →
      W = Matrix.kronecker X Y → extendedConditional A B W = extendedMin B Y) ∧
    (∀ (C D : System) (Z : Mat (ChoiRegister C × ChoiRegister D)), BipartiteChannel C D Z →
      extendedConditional (productSystem A C) (productSystem B D) (productBipartite W Z) =
        extendedConditional A B W + extendedConditional C D Z) ∧
    (∀ (C : System) (T : Supermap A C), IsSuperchannel T →
      extendedConditional A B W ≤ extendedConditional C B (localApply T B W)) ∧
    (∀ (C : System) (Z : Mat (ChoiRegister (productSystem A C) × ChoiRegister B)) (R : Mat (In C)),
      BipartiteChannel (productSystem A C) B Z → QAlgorithms.IsDensityMatrix R →
      extendedConditional (productSystem A C) B Z ≤ extendedConditional A B (discardConditioner Z R)) ∧
    (extendedConditional A B W ≤ stateConditional (outputMarginal W) ∧
      stateConditional (lowerBoundState W) - (Real.logb 2 (A.input * A.output) : EReal) ≤
        extendedConditional A B W) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
