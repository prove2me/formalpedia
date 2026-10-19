-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_complete_unital_equivalences
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.complete_unital_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:56:12.306987+00:00
-- url     : https://prove2.me/theorems/ebd96304-38cb-49a7-b8b6-ca4e316f54ce
-- title:
--   Complete unital preservation: Choi and joint-channel characterizations
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Assume $d_{A_0}=d_{A_1}$ and $d_{B_0}=d_{B_1}$. The following are equivalent for a superchannel $\Theta$:
--
--   1. Every extension by an auxiliary system with equal input/output dimensions preserves all unital channels.
--   2. Positivity and Eq.(19) hold, and $J^{AB_1}=u^{A_0}\otimes J^{A_1B_1}$ and $J^{A_0B_1}=I$.
--   3. The channel $\Gamma_\Theta:A_1B_0\to A_0B_1$, obtained by reshaping the same Choi matrix, is unital, its $A_0$ marginal has the form $K^{B_0\to A_0}\circ\operatorname{Tr}_{A_1}$ for a CPTP map $K$, and for every density matrix $R$ on $A_1$,
--   $$\Gamma_\Theta(R\otimes u^{B_0})=u^{A_0}\otimes\operatorname{Tr}_{A_0}\Gamma_\Theta(R\otimes u^{B_0}).$$
--   This preserves the full joint output in the physical characterization.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 11, Theorem 4, Eq.(59)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.11–12, Theorem 4. Includes both Choi conditions, the full
joint output in Eq.(59), and the ordinary Gamma marginal in Eq.(31). -/
theorem complete_unital_equivalences {A B : System} (ha : A.input = A.output)
    (hb : B.input = B.output) (T : Supermap A B) (hT : IsSuperchannel T) :
    (CompletelyUnitalPreserving T ↔
      StandardMarginals T ∧ UnitalFactorization T ∧ jA0B1 T = 1) ∧
    (CompletelyUnitalPreserving T ↔ ChannelChoi (gammaChoi T) ∧ Unital (gammaChoi T) ∧
      GammaMarginal T ∧ GammaUniformInput T) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
