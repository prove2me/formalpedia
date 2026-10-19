-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_quantum_input_guessing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.quantum_input_guessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:05:25.861819+00:00
-- url     : https://prove2.me/theorems/ed6a5aea-5108-4340-9290-50e536c3fbaf
-- title:
--   Quantum-input guessing from a normalized Bell pair
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\Omega^{AB}$ be a channel classical only on $B_1$, with CP instrument branches $\Omega_x:A_0B_0\to A_1$. Let $A_2$ be a copy of $B_0$. Optimize over isometries $V:\widetilde A_2\to A_0\widetilde A_0\widetilde B_0$ and complete POVMs $\{P_x\}$ on $A_0A_2A_1$. Set $|\eta_V\rangle=(\mathrm{id}_{A_2}\otimes V)|\phi_+\rangle/\sqrt{d_{A_2}}$. Then the maximum is attained and
--   $$\max_{V,\{P_x\}}\sum_x\operatorname{Tr}\!\left[P_x(\mathrm{id}_{A_0A_2}\otimes\Omega_x)(|\eta_V\rangle\langle\eta_V|)\right]=2^{-H_{\min}^{\rm ext}(B|A)_\Omega}.$$
--   The POVM conditions are $P_x\ge0$ and $\sum_xP_x=I$. The isometry may mix the original inputs jointly. This is the operational optimization depicted in Fig.6, with normalized initial entanglement and subnormalized instrument branches.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 23, Appendix B, Eqs.(109)–(112)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.16–17,22–23, Appendix B, Eqs.(109)–(112): quantum-input
operational guessing, including POVM completeness omitted from the final printed display.
V is a joint isometry, not a local separated-party operation; Bell input is normalized. -/
theorem quantum_input_guessing (A B : System) (W : Mat (ChoiRegister A × ChoiRegister B))
    (hW : BipartiteChannel A B W) (hc : ClassicalOutput W) :
    quantumGuessProbability W = entropyPower (extendedConditional A B W) ∧
    ∃ s : QuantumGuessStrategy A B, (quantumGuessScore W s : EReal) = quantumGuessProbability W := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
