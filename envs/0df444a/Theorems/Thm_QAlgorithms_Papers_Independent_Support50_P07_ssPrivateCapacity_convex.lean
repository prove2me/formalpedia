-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssPrivateCapacity_convex
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssPrivateCapacity_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:45:38.198266+00:00
-- url     : https://prove2.me/theorems/2e23eee2-2ee7-4dc0-96a7-869e8b0dcc76
-- title:
--   Lemma 8: convexity of operational ss-private capacity
-- statement:
--   Let $\mathcal N_0,\mathcal N_1:A\to B$ have compatible input and receiver spaces, and let $0\le p\le1$. Let $\mathcal M$ be any Stinespring realization of the receiver map $(1-p)\mathcal N_0+p\mathcal N_1$. Then
--
--   $$C_{p,ss}(\mathcal M)\le(1-p)C_{p,ss}(\mathcal N_0)+pC_{p,ss}(\mathcal N_1).$$
--
--   Each operational capacity uses its channel's full complementary output.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 5, Lemma 8: convexity of operational ss-private capacity

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

/-- Lemma 8, PDF p.5: convexity compares RECEIVER maps. Each channel's full
complementaryChannel comes from its own isometry; no mixture of isometries is taken. -/
theorem ssPrivateCapacity_convex [Nonempty A] [Nonempty B] [Nonempty E]
    {G H : Type} [Fintype G] [DecidableEq G]
    [Nonempty G] [Fintype H] [DecidableEq H] [Nonempty H]
    (U : Matrix (B × E) A ℂ) (V : Matrix (B × G) A ℂ)
    (W : Matrix (B × H) A ℂ) (hU : IsIsometry U) (hV : IsIsometry V)
    (hW : IsIsometry W) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hmix : ∀ rho, receiverChannel W rho = ((1 - p : ℝ) : ℂ) • receiverChannel U rho +
      (p : ℂ) • receiverChannel V rho) :
    ssPrivateCapacity W ≤ (1 - p) * ssPrivateCapacity U + p * ssPrivateCapacity V := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
