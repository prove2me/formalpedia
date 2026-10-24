-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_twoKraus_privateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.twoKraus_privateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:53:48.651977+00:00
-- url     : https://prove2.me/theorems/88a29582-2d01-4873-b94f-81081d7e36c5
-- title:
--   Section IV.A: private capacity of the two-Kraus qubit family
-- statement:
--   For $\gamma,\delta\in[0,1]$, let $\mathcal N_{\gamma,\delta}$ have Kraus matrices $A_0=\operatorname{diag}(\sqrt{1-\gamma},\sqrt{1-\delta})$ and $A_1=\begin{pmatrix}0&\sqrt\delta\\\sqrt\gamma&0\end{pmatrix}$. Then
--
--   $$C_p(\mathcal N_{\gamma,\delta})=\max_{0\le t\le1}\{H(t(1-\gamma)+(1-t)\delta)-H(t\gamma+(1-t)\delta)\}.$$
--
--   The maximum is attained, including in the antidegradable regime.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 6, Section IV.A: private capacity of the two-Kraus qubit family

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

/-- Section IV.A, PDF p.6: optimized formula for all physical two-Kraus parameters,
including the antidegradable regime. The existential t records the printed MAX, not just a supremum. -/
theorem twoKraus_privateCapacity [Nonempty E]
    (U : Matrix (Fin 2 × E) (Fin 2) ℂ)
    (hU : IsIsometry U) (gamma delta : ℝ)
    (hg : gamma ∈ Set.Icc 0 1) (hd : delta ∈ Set.Icc 0 1)
    (hmap : receiverChannel U = twoKrausChannel gamma delta) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧
      fullTracePrivateCapacity U = twoKrausValue gamma delta t ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, twoKrausValue gamma delta s ≤ twoKrausValue gamma delta t := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
