-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_minimum_output_monotonicity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.minimum_output_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:56:45.580696+00:00
-- url     : https://prove2.me/theorems/cd667cb1-3ffc-4bbf-ab60-42a5797261df
-- title:
--   Monotonicity of minimum output Renyi entropy
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. All entropy logarithms are base two. Let $\Theta$ be a random-unitary superchannel between systems whose input and output dimensions match separately, let $\Phi$ be a channel, and let $0\le\alpha\le1$. For a density matrix $R$, let $H_0(R)=\log_2\operatorname{rank}R$, $H_1(R)=-\operatorname{Tr}(R\log_2R)$, and $H_\alpha(R)=\log_2\operatorname{Tr}(R^\alpha)/(1-\alpha)$ otherwise. Then both displayed minima are attained and
--   $$\min_{\rho\in D(B_0)}H_\alpha(\Theta[\Phi](\rho))\ \ge\ \min_{\rho\in D(A_0)}H_\alpha(\Phi(\rho)).$$
--   This includes von Neumann minimum-output entropy. No additivity assertion is made.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 12, Sec. IV, minimum-output entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.12, Sec.IV: minimum-output entropy is monotone for every
Renyi order in [0,1], including the von Neumann case, with the minima attained. No additivity. -/
theorem minimum_output_monotonicity {A B : System} (hin : A.input = B.input)
    (hout : A.output = B.output) (T : Supermap A B) (hT : IsRandomUnitary T)
    (X : Mat (ChoiRegister A)) (hX : ChannelChoi X) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    minimumOutput A a X ≤ minimumOutput B a (T X) ∧
    (∃ R : Mat (In A), QAlgorithms.IsDensityMatrix R ∧ renyiEntropy a (action X R) = minimumOutput A a X) ∧
    (∃ R : Mat (In B), QAlgorithms.IsDensityMatrix R ∧ renyiEntropy a (action (T X) R) =
      minimumOutput B a (T X)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
