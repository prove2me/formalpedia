-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_extended_min_entropy
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.extended_min_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:57:16.591768+00:00
-- url     : https://prove2.me/theorems/5e525209-16e0-4b41-b5a1-cf714565e8c9
-- title:
--   Extended min-entropy satisfies the three channel-entropy axioms
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Define $H_{\min}^{\rm ext}(A)_\Phi=H_{\min}(A_1|A_0)_{J_\Phi/d_{A_0}}$, using the primal state conditional min-entropy, with base-two logarithms. Then:
--
--   1. For every doubly stochastic superchannel $\Theta:A\to B$ with separately matched input and output dimensions and every channel $\Phi$,
--   $$H_{\min}^{\rm ext}(A)_\Phi\le H_{\min}^{\rm ext}(B)_{\Theta[\Phi]}.$$
--   2. For arbitrary channels $\Phi^A,\Psi^B$, $H_{\min}^{\rm ext}(AB)_{\Phi\otimes\Psi}=H_{\min}^{\rm ext}(A)_\Phi+H_{\min}^{\rm ext}(B)_\Psi$.
--   3. The uniform channel has entropy $\log_2d_{A_1}$, and every replacement channel with a fixed unit-vector pure output has entropy zero.
--
--   These are monotonicity, additivity and normalization, with the stronger monotonicity proved in Eq.(61).
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 13, Definition 3 and Eq.(61)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.12–13, Definition 3 and Eq.(61): all three entropy axioms,
with stronger monotonicity for doubly stochastic superchannels on isomorphic systems. -/
theorem extended_min_entropy (A : System) :
    (∀ (B : System), A.input = B.input → A.output = B.output →
      ∀ T : Supermap A B, IsDoublyStochastic T →
        ∀ X : Mat (ChoiRegister A), ChannelChoi X → extendedMin A X ≤ extendedMin B (T X)) ∧
    (∀ (B : System) (X : Mat (ChoiRegister A)) (Y : Mat (ChoiRegister B)),
      ChannelChoi X → ChannelChoi Y →
      extendedMin (productSystem A B) (productChoi X Y) = extendedMin A X + extendedMin B Y) ∧
    extendedMin A (uniformChannel A) = (Real.logb 2 A.output : EReal) ∧
    (∀ v : Out A → ℂ, (∑ i, Complex.normSq (v i)) = 1 →
      extendedMin A (Matrix.kronecker (1 : Mat (In A)) (ketProjector v)) = 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
