-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_Supplement_lemma_3_2
-- name    : RandomDimReduction.Channel.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:42:18.567443+00:00
-- url     : https://prove2.me/theorems/c8d4a79b-83dc-463d-9692-043e227f9b38
-- title:
--   Lemma 3.2 — complete positivity of commuting multiplication
-- statement:
--   Let $H$ be any complex Hilbert space, $S\subseteq L(H)$ a complex subalgebra of bounded operators, and $A\in L(H)$ positive. Suppose $XA=AX$ for every $X\in S$. Then
--   $$f:S\to L(H),\qquad f(X)=AX$$
--   is completely positive for the inherited matrix order at every finite amplification. There is no finite-dimensionality, commutativity, norm-closure or star-closure requirement on $S$, and $A$ need not belong to $S$.
--
--   This is the positivity criterion used for the exchangeable-operator restriction of the explicit purification extension.
--
--   Differences from the source:
--   - generalization: a complex subalgebra S → a possibly nonunital complex subalgebra S; reason: no identity is used in the criterion; every unital subalgebra is covered by forgetting its unit condition
--   - encoding: operators on some complex Hilbert space and CP on a subalgebra → bounded operators on any complete complex inner product space, with self-adjoint positive block matrices at every finite amplification; reason: this is the inherited matrix order on the Hilbert direct sums and does not assume finite dimension or a diagonal eigenbasis
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, Lemma 3.2, p. 9

import Definitions.Def_RandomDimReduction_Channel_Supplement_SubalgebraCP

set_option autoImplicit false
noncomputable section

namespace RandomDimReduction.Channel.Supplement

/-- Lemma 3.2, p.9, on arbitrary complex Hilbert spaces, using bounded operators.
Neither A ∈ S nor a star-closure or finite-dimensionality assumption is required. -/
theorem lemma_3_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (S : NonUnitalSubalgebra ℂ (H →L[ℂ] H))
    (hA : A.IsPositive) (hcomm : ∀ X : S, (X : H →L[ℂ] H) * A = A * (X : H →L[ℂ] H)) :
    CompletelyPositiveOn S (leftMultiplication S A) := by sorry

end RandomDimReduction.Channel.Supplement
