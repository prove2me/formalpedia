-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_operational_guessing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.operational_guessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:59:34.464979+00:00
-- url     : https://prove2.me/theorems/051081da-2775-4f09-8863-98bfd0f85e3a
-- title:
--   Uniform-input guessing and channel discrimination
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\Omega^{AB}$ be a channel classical on both $B_0$ and $B_1$. Its conditional branches $\Omega_{x|y}:A_0\to A_1$ are CP and sum over $x$ to a channel for every $y$. For known $y$, optimize over a unit vector $\eta_y$ on $A_2A_0$ with $d_{A_2}=d_{A_0}$ and a complete POVM $\{P_{x|y}\}$ on $A_2A_1$. Then
--   $$P_{\rm guess}(\Omega)=\frac1{d_{B_0}}\sum_y\max_{\eta_y,\{P_{x|y}\}}\sum_x\operatorname{Tr}\!\left[P_{x|y}(\mathrm{id}_{A_2}\otimes\Omega_{x|y})(|\eta_y\rangle\langle\eta_y|)\right]=2^{-H_{\min}^{\rm ext}(B|A)_\Omega}.$$
--   Every conditional maximum is attained. When $\Omega_{x|y}=p_x\Lambda_{x|y}$ for a probability vector $p$ and CPTP maps $\Lambda_{x|y}$, the same value is the uniform-in-$y$ optimal entanglement-assisted discrimination probability with prior $p_x$. Branches retain their subnormalization. This is an average of optimizations for the known input, not a single strategy independent of that input.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 16, Theorem 6, Eqs.(82)–(86)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.15–16, Theorem 6 and the channel-discrimination specialization.
The strategy depends on the known y; the average is uniformDensity, not worst-case. -/
theorem operational_guessing (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B))
    (hW : BipartiteChannel A B W) (hc : ClassicalSystem W) :
    guessProbability W = entropyPower (extendedConditional A B W) ∧
    (∀ y : In B, ∃ s : GuessStrategy A B,
      (guessScore W y s : EReal) = ⨆ t : GuessStrategy A B, (guessScore W y t : EReal)) ∧
    (∀ (p : Out B → ℝ) (L : In B → Out B → Mat (ChoiRegister A)),
      (∀ x, 0 ≤ p x) → (∑ x, p x = 1) → (∀ y x, ChannelChoi (L y x)) →
      (∀ y x, classicalBranch W y x = (p x : ℂ) • L y x) →
      guessProbability W = discriminationProbability A B p L) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
