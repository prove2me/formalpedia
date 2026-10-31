-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_arbitrary_preimage_sizes
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.arbitrary_preimage_sizes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:58:32.866541+00:00
-- url     : https://prove2.me/theorems/1fecebf4-73d8-407f-9c6c-624c5fc69c4c
-- title:
--   A typical attained fiber is large under the pushforward law
-- statement:
--   Let $X$ and $Y$ be finite nonempty sets, let $f:X\to Y$ be arbitrary, and let $0\le\varepsilon\le1$. Draw $x$ uniformly from $X$ and set $y=f(x)$. Then
--
--   $$
--   \Pr\!\left[|f^{-1}(y)|\ge\frac{\varepsilon|X|}{|Y|}\right]\ge1-\varepsilon.
--   $$
--
--   The probability is taken under the pushforward of the uniform input law, not under a uniform draw from the codomain. This provides the large-fiber estimate relevant to nonlinear compression.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 7, Lemma 4: Preimage Sizes of Arbitrary Functions

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

/-- Lemma 4, PDF p.7: first draw x uniformly and then use y=f(x). The
codomain is not sampled uniformly; empty fibers have mass zero. -/
theorem arbitrary_preimage_sizes [Nonempty X] [Nonempty Y]
    (f : X → Y) (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) :
    1 - epsilon ≤ (Fintype.card X : ℝ)⁻¹ *
      ∑ x : X, if epsilon * (Fintype.card X : ℝ) / (Fintype.card Y : ℝ) ≤
        (Fintype.card {a : X // f a = f x} : ℝ) then 1 else 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
