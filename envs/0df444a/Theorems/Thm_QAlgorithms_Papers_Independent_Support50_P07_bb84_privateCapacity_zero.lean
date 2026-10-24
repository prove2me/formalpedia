-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_bb84_privateCapacity_zero
-- name    : QAlgorithms.Papers.Independent.Support50.P07.bb84_privateCapacity_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:57:57.268405+00:00
-- url     : https://prove2.me/theorems/7abffa23-a112-4e40-8813-00c57a71239d
-- title:
--   Section IV.B: no-key threshold on the BB84 noise branch
-- statement:
--   For $\frac12(1-1/\sqrt2)\le q\le1/2$, let $\mathcal N_q$ be the independent phase/amplitude Pauli channel with probabilities $(1-q)^2,q(1-q),q^2,q(1-q)$ for $I,X,Y,Z$, respectively. Then
--
--   $$C_p(\mathcal N_q)=0.$$
--
--   This is the channel-capacity no-key implication on the conventional BB84 low-noise branch.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 6, Section IV.B: no-key threshold on the BB84 noise branch

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

/-- Section IV.B, PDF p.6: zero channel private capacity at and above the BB84
threshold on the conventional low-noise branch. SOURCE DOMAIN CLARIFICATION:
the printed word "beyond" is restricted to q<=1/2, the preceding construction's branch;
at q=1 the channel is unitary Y and has positive capacity. This states the capacity
implication; no additional individual/collective attack model is presumed. -/
theorem bb84_privateCapacity_zero [Nonempty E]
    (U : Matrix (Fin 2 × E) (Fin 2) ℂ)
    (hU : IsIsometry U) (q : ℝ)
    (hq : q ∈ Set.Icc ((1 - 1 / Real.sqrt 2) / 2) (1 / 2))
    (hmap : receiverChannel U = independentPauliChannel q) :
    fullTracePrivateCapacity U = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
