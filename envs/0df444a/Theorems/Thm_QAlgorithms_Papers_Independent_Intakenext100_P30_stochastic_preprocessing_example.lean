-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_stochastic_preprocessing_example
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.stochastic_preprocessing_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:57:19.04202+00:00
-- url     : https://prove2.me/theorems/c8a3a0ae-2feb-4a8e-9d4b-61a4ebac7604
-- title:
--   Stochastic preprocessing strictly improves the Figure 2 private-information expression
-- statement:
--   Consider the classical channel on $X=\{0,1,2\}$ with deterministic receiver outputs $Y(0)=Y(1)=0$, $Y(2)=1$, and eavesdropper outputs $Z(0)=0$, $Z(1)=1$, with $Z(2)$ a fair bit. Encode message $0$ uniformly as $X=0$ or $X=1$, and message $1$ as $X=2$. Both conditional encoding laws are normalized and nonnegative. For each message $m$, the receiver output is exactly $m$ and Eve's output is the fair distribution, so this transmits one private bit without error. Moreover,
--
--   $$
--   \sup_{P_X}\bigl[H(X|Z)-H(X|Y)\bigr]<1.
--   $$
--
--   The strict inequality concerns the maximum over the full input simplex, not merely pointwise inequality for each law. This example establishes the need to optimize stochastic preprocessing in the private-information expression.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 6, §IV Figure 2: stochastic preprocessing improves the private-information expression

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

/-- Figure 2 and following paragraph, PDF p.6: the concrete stochastic encoder
transmits a bit perfectly with identical fair Eve outputs, whereas the optimized
unpreprocessed private information is strictly smaller than one bit. No new
operational notion of deterministic-encoding capacity is asserted. -/
theorem stochastic_preprocessing_example :
    (∀ message : Bool,
      (∑ x : Fin 3, rrExampleEncoder message x = 1) ∧
      (∀ x, 0 ≤ rrExampleEncoder message x) ∧
      (∑ x : Fin 3, (rrExampleEncoder message x : ℂ) • rrExampleReceiver x) =
        Matrix.diagonal (fun y => if y = message then (1 : ℂ) else 0) ∧
      (∑ x : Fin 3, (rrExampleEncoder message x : ℂ) • rrExampleEve x) =
        Matrix.diagonal (fun _ => (1 / 2 : ℂ))) ∧
    rrExampleUnprocessedInformation < (1 : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
