-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_linear_preimage_sizes
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.linear_preimage_sizes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:57:52.123007+00:00
-- url     : https://prove2.me/theorems/b4c0fbf1-52d3-4164-a366-f6d70280c4b6
-- title:
--   Equal fiber sizes for a surjective linear map
-- statement:
--   Let $U$ and $V$ be finite vector spaces over the same field and let $f:U\to V$ be a surjective linear map. Then every $v\in V$ satisfies
--
--   $$
--   |f^{-1}(v)|=\frac{|U|}{|V|}.
--   $$
--
--   The cardinalities in the displayed quotient are real numbers, so no truncated natural division is involved. This is the equal-fiber fact used by the channel-code construction when the compression alphabet is its actual range.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 7, Lemma 3: Preimage Sizes of Linear Functions (onto-range correction)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakenext100.P30

variable {X Y Z M U V A B C : Type*}

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]

variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C]

attribute [local instance] Classical.propDecidable

/-- Lemma 3, PDF p.7: onto-range correction. The printed statement omits
surjectivity and fails for the zero map F2→F2. The proof and section II.B use
attained outputs; all fibers of an onto linear map have this size. -/
theorem linear_preimage_sizes {K : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f : U →ₗ[K] V) (honto : Function.Surjective f) (v : V) :
    (Fintype.card {u : U // f u = v} : ℝ) =
      (Fintype.card U : ℝ) / (Fintype.card V : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
