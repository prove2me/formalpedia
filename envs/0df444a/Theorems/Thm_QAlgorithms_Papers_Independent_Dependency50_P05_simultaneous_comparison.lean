-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_simultaneous_comparison
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.simultaneous_comparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:02:04.958724+00:00
-- url     : https://prove2.me/theorems/45bbe96b-7bec-4564-81c2-72ecbc0110f8
-- title:
--   Simultaneous comparison of arbitrary positive finite channel families
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $n\ge1$, let $\Psi_j^A,\Phi_j^B$ be channels for $1\le j\le n$, and identify the test system $R$ with a fixed-basis copy of $B$, matching its input and output dimensions separately. A single superchannel $\Theta$ with $\Theta[\Psi_j]=\Phi_j$ for every $j$ exists if and only if every channel family $\Lambda_j^R$ satisfies
--   $$H_{\min}^{\rm ext}(R|A)_{\frac1n\sum_j\Psi_j\otimes\Lambda_j}\le H_{\min}^{\rm ext}(R|B)_{\frac1n\sum_j\Phi_j\otimes\Lambda_j}.$$
--   The two bipartite channels are exactly the marginals of the source's tripartite mixture $n^{-1}\sum_j\Psi_j\otimes\Phi_j\otimes\Lambda_j$; the unused local factor is TP, so inserting any input state and tracing its output yields these marginals. The criterion compares the whole family using one common transformation.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 20, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.20, Corollary 1: one COMMON superchannel for all members of
an arbitrary positive finite family. The test system is the fixed-basis identical copy of B. -/
theorem simultaneous_comparison (A B : System) (n : ℕ) (hn : 0 < n)
    (X : Fin n → Mat (ChoiRegister A)) (Y : Fin n → Mat (ChoiRegister B))
    (hX : ∀ j, ChannelChoi (X j)) (hY : ∀ j, ChannelChoi (Y j)) :
    (∃ T : Supermap A B, IsSuperchannel T ∧ ∀ j, T (X j) = Y j) ↔
    ∀ K : Fin n → Mat (ChoiRegister B), (∀ j, ChannelChoi (K j)) →
      extendedConditional A B (familyMixture X K) ≤ extendedConditional B B (familyMixture Y K) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
