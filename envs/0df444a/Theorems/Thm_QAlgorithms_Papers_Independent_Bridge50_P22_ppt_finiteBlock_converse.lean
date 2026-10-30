-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_ppt_finiteBlock_converse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.ppt_finiteBlock_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:12:11.918173+00:00
-- url     : https://prove2.me/theorems/786f5c2d-418e-4a93-8e8f-063ada572adb
-- title:
--   Finite-block PPT-preserving-assisted communication converse
-- statement:
--   Let $\mathcal N_{A\to B}$ be a finite-dimensional quantum channel, let $n,M\ge1$ be integers, and let $0<\varepsilon<1$. Consider a protocol with $n$ uses of this same channel, arbitrary positive finite local memories, a PPT-preserving preparation from the trivial system, PPT-preserving operations between channel uses, and a final PPT-preserving decoder. Here a map is PPT-preserving when both it and its conjugate by Bob's input and output partial transposes are completely positive and trace preserving. Let $\omega_{M_AM_B}$ be the computed output, where both output dimensions are $M$, and suppose its squared fidelity with the normalized maximally entangled state $\Phi_M$ is $\operatorname{Tr}(\Phi_M\omega)\ge1-\varepsilon$. With $R_{\max}(\mathcal N)$ denoting the channel's max-Rains information in bits,
--
--   $$\log_2 M\le nR_{\max}(\mathcal N)+\log_2\frac1{1-\varepsilon}.$$
--
--   The bound applies to concrete adaptive protocols and allows no initial shared resource beyond the free PPT-preserving preparation.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 11, Theorem 3 / eq. (53)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P22

open QAlgorithms QAlgorithms.Entanglement Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (Le eMax)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pptPrime target)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P04 (IsPPTChannel)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section Statements

variable {A B C D L R : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype L] [Fintype R]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq L] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty L] [Nonempty R]

/-- Theorem 3, PDF pp.11–12, (53): finite-block PPT-P-assisted converse.
Protocol semantics count actual channel uses and construct the initial free state.
The right-hand logarithm is defined on a positive argument since 0<epsilon<1. -/
theorem ppt_finiteBlock_converse (N : Superop A B) (hN : IsChannel N)
    (n M : ℕ) (hn : 0 < n) (hM : 0 < M) (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (protocol : IsPPTProtocol N n M epsilon) :
    (Real.logb 2 (M : ℝ) : EReal) ≤
      (n : EReal) * channelMaxRains N +
        (Real.logb 2 (1 / (1 - epsilon)) : EReal) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
