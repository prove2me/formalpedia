-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_amplitudeDamping_privateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.amplitudeDamping_privateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:55:38.400828+00:00
-- url     : https://prove2.me/theorems/d7e7eee1-d399-4007-a6b7-ff860c253156
-- title:
--   Section IV.A–B: amplitude-damping private capacity
-- statement:
--   For $\gamma\in[0,1]$, let $\mathcal A_\gamma$ be amplitude damping with Kraus matrices $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma|0\rangle\langle1|$. Then
--
--   $$C_p(\mathcal A_\gamma)=f(\gamma):=\max_{0\le t\le1}[H(t(1-\gamma))-H(t\gamma)].$$
--
--   The maximum is attained; it equals zero for $\gamma\ge1/2$.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 6, Section IV.A–B: amplitude-damping private capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P07

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
    dilationPower idealJoint maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

variable {A B E C D F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

/-- Section IV.B, PDF p.6: all physical damping parameters; maximum is attained,
and is zero in the antidegradable regime. t exchanges populations relative to IV.A. -/
theorem amplitudeDamping_privateCapacity [Nonempty E]
    (U : Matrix (Fin 2 × E) (Fin 2) ℂ)
    (hU : IsIsometry U) (gamma : ℝ) (hg : gamma ∈ Set.Icc 0 1)
    (hmap : receiverChannel U = amplitudeDampingChannel gamma) :
    fullTracePrivateCapacity U = dampingBound gamma ∧
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ dampingBound gamma =
      binEntropy2 (t * (1 - gamma)) - binEntropy2 (t * gamma) := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
