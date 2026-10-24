-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_ssEquality_iff_privateAdditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.ssEquality_iff_privateAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:59:31.66066+00:00
-- url     : https://prove2.me/theorems/69af2b25-4c79-472e-b1b3-c8a5290726cc
-- title:
--   Section V: equivalence of ss equality and private-capacity additivity
-- statement:
--   The following two universal propositions, each ranging over all finite nonzero quantum channels, are equivalent:
--
--   $$[\forall\mathcal N,\ C_{p,ss}(\mathcal N)=C_p(\mathcal N)]\quad\Longleftrightarrow\quad[\forall\mathcal N_1,\mathcal N_2,\ C_p(\mathcal N_1\otimes\mathcal N_2)=C_p(\mathcal N_1)+C_p(\mathcal N_2)].$$
--
--   The statement asserts the equivalence, not the truth of either conjecture.
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 8, Section V: equivalence of ss equality and private-capacity additivity

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

/-- Section V, PDF p.8: equivalence of two universally quantified conjectures.
Neither proposition is asserted true; all finite nonzero input/output/environment
sizes are quantified separately, and the product inputs can be entangled. -/
theorem ssEquality_iff_privateAdditivity :
    (∀ a b e : ℕ, 0 < a → 0 < b → 0 < e →
      ∀ U : Matrix (Fin b × Fin e) (Fin a) ℂ, IsIsometry U →
        ssPrivateCapacity U = fullTracePrivateCapacity U) ↔
    (∀ a b e c d f : ℕ, 0 < a → 0 < b → 0 < e → 0 < c → 0 < d → 0 < f →
      ∀ (U : Matrix (Fin b × Fin e) (Fin a) ℂ)
        (V : Matrix (Fin d × Fin f) (Fin c) ℂ), IsIsometry U → IsIsometry V →
        fullTracePrivateCapacity (productDilation U V) = fullTracePrivateCapacity U + fullTracePrivateCapacity V) := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
