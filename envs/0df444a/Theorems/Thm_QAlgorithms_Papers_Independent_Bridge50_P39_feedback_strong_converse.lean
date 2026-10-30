-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P39_feedback_strong_converse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P39.feedback_strong_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:49:58.532689+00:00
-- url     : https://prove2.me/theorems/eb1f8128-ea48-4005-a946-b7daa37e94aa
-- title:
--   One positive decay exponent uniformly over all valid feedback codes
-- statement:
--   Let $\mathcal N:A\to B$ be a quantum channel between positive, finite-dimensional complex Hilbert spaces and fix a rate $R>\chi(\mathcal N)$, where $\chi(\mathcal N)$ is its single-use Holevo information optimized over all finite mixed-state input ensembles, with base-two entropy. Then there exists a constant $c=c(\mathcal N,R)>0$ such that, for every $n\ge1$, every finite message count $L\ge1$ and every valid $n$-use classical-feedback protocol $P$ with $R\le\log_2 L/n$,
--
--   $$
--   p_{\mathrm{succ}}(P)\le2^{-cn},
--   $$
--
--   provided either $\mathcal N$ is entanglement-breaking or each actual encoded conditional state, for every message and past classical transcript before each individual use, is fully separable across retained Alice memory, current input and Bob memory. In the entanglement-breaking alternative the encoding is unrestricted. Protocols have arbitrary finite local memories, initial noiseless classical feedback $X_0$, no initially shared entanglement or message-dependent Bob seed, and a final $L$-outcome POVM. Success is the uniform-message average of the correct-message Born probabilities of the executed output.
--
--   The constant is chosen before blocklengths and codes. Consequently every sequence with liminf rate strictly greater than $\chi(\mathcal N)$ has the same exponential decay eventually, by fixing an intermediate rate $R$. The threshold in the general separable-input case is the Holevo information.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, PDF p. 14, Corollary 6; (4.53)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- PDF p.14, Corollary 6 and (4.53): one positive exponent depends only on N,R,
uniformly over all blocklengths, messages, memories and valid codes of rate at least R.
A sequence with liminf rate above chi satisfies a fixed intermediate R eventually. -/
theorem feedback_strong_converse [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N)
    (R : ℝ) (hR : channelHolevo N < R) :
    ∃ c : ℝ, 0 < c ∧ ∀ n L : ℕ, ∀ P : FeedbackCode A B n L,
      P.Valid → (IsEB N ∨ P.SeparableInputs N) → R ≤ uniformMessageRate n L →
      P.success N ≤ (2 : ℝ) ^ (-(c * (n : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P39

end
