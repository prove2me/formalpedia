-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_erasure_privateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.erasure_privateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:56:31.858978+00:00
-- url     : https://prove2.me/theorems/7c7d8a4a-674e-4fe4-afb2-7264c2ae83e6
-- title:
--   Section IV.A: private capacity of a degradable erasure channel (domain correction)
-- statement:
--   Let $d\ge1$ and $0\le p\le1/2$. The erasure channel sends an input density operator on $\mathbb C^d$ to $(1-p)\rho+p|e\rangle\langle e|$, where the erasure flag is orthogonal to the input subspace. Then
--
--   $$C_p(\mathcal E_{p,d})=Q(\mathcal E_{p,d})=(1-2p)\log_2 d.$$
--
--   This is the degradable parameter range used by the source's argument.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 6, Section IV.A: private capacity of a degradable erasure channel (domain correction)

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

/-- Section IV.A, PDF p.6, SOURCE DOMAIN CORRECTION: the printed sentence calls
all erasure channels degradable. The argument requires p<=1/2; at d=2,p=1 the printed
RHS is -1. Restrict to the degradable range and retain the positive input dimension. -/
theorem erasure_privateCapacity [Nonempty E]
    (d : ℕ) (hd : 0 < d)
    (U : Matrix (Option (Fin d) × E) (Fin d) ℂ) (hU : IsIsometry U)
    (p : ℝ) (hp : p ∈ Set.Icc 0 (1 / 2)) (hmap : receiverChannel U = erasureMap d p) :
    fullTracePrivateCapacity U = (1 - 2 * p) * Real.logb 2 d ∧
    QAlgorithms.Papers.Independent.Information100.P80.quantumCapacity (receiverChannel U) =
      (1 - 2 * p) * Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
