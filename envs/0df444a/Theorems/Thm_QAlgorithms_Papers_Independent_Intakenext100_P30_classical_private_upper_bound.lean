-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_classical_private_upper_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.classical_private_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:59:03.612694+00:00
-- url     : https://prove2.me/theorems/a08e398d-7192-47e5-8489-29c37e4ff193
-- title:
--   Classical private rate is bounded by the single-letter private information
-- statement:
--   For a cq channel whose receiver states and eavesdropper states are each simultaneously diagonalizable, the private operational iterated rate exists and obeys
--
--   $$
--   R_{\rm prv}(\Theta)\le\sup_{P_T,T\to X}\bigl[H(T|Z)-H(T|Y)\bigr].
--   $$
--
--   The supremum ranges over all finite nonempty auxiliaries, their laws, and stochastic encoders, with the same fixed classical-output channel. The operational secrecy criterion is messagewise half trace norm distance to a single normalized reference. This is the numbered one-sided bound (37), kept distinct from the equality in (19).
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
--
--   The single-letter information maximum is attained by some finite nonempty auxiliary with a normalized law and stochastic preprocessor; this optimizer is a conclusion.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 8, Lemma 6: Single-Letter Formula for the Private Capacity

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

/-- Lemma 6, PDF p.8, (37): the printed one-sided classical private-capacity
bound. The operational rate exists, and is at most the attained single-letter
private information maximum. Its optimizer is a conclusion, with no size cutoff.
No telescoping or conditional Markov identity is assumed. -/
theorem classical_private_upper_bound [Nonempty X] [Nonempty Y] [Nonempty Z]
    (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (hY : RRIsCq thetaY) (hZ : RRIsCq thetaZ)
    (hclassicalY : RRClassicalOutputs thetaY) (hclassicalZ : RRClassicalOutputs thetaZ) :
    ∃ rate : ℝ, RRPrivateRate thetaY thetaZ rate ∧
      (rate : EReal) ≤ rrPrivateInformation thetaY thetaZ ∧
      ∃ k : ℕ, ∃ p : RRDistribution (Fin (k + 1)),
        ∃ enc : Fin (k + 1) → RRDistribution X,
          (rrConditionalEntropy (rrCqState p.prob (rrPreprocess thetaZ enc)) -
            rrConditionalEntropy (rrCqState p.prob (rrPreprocess thetaY enc)) : EReal) =
              rrPrivateInformation thetaY thetaZ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
