-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_classical_private_rate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.classical_private_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:56:40.171981+00:00
-- url     : https://prove2.me/theorems/c7e24a02-07f1-4353-8acd-209619c49544
-- title:
--   Single-letter private rate for classical outputs
-- statement:
--   Suppose the receiver output family and the eavesdropper output family are each simultaneously diagonalizable, separately, in fixed orthonormal bases. The private operational iterated limit exists and satisfies
--
--   $$
--   R_{\rm prv}(\Theta)=\sup_{P_T,T\to X}\bigl[H(T|Z)-H(T|Y)\bigr].
--   $$
--
--   Here $T$ is any finite nonempty auxiliary, $P_T$ any law, and $T\to X$ any stochastic map, followed by the fixed channel. The operational rate uses the source's messagewise decoding and trace-distance secrecy conditions. This removes regularization for classical outputs while retaining essential stochastic preprocessing.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
--
--   The maximum is attained by some finite nonempty auxiliary alphabet, a normalized law on it, and a stochastic preprocessor into $X$. Their private information equals the operational rate; no cardinality cutoff is assumed.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 5, §IV (19): classical single-letter private rate

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

/-- Section IV, PDF p.5, (19): classical-output single-letter private rate.
Each marginal is simultaneously diagonalizable separately. Stochastic
preprocessing is optimized, and both operational limits exist. An attaining
finite auxiliary and stochastic preprocessor are conclusions, with no size cutoff. -/
theorem classical_private_rate [Nonempty X] [Nonempty Y] [Nonempty Z]
    (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (hY : RRIsCq thetaY) (hZ : RRIsCq thetaZ)
    (hclassicalY : RRClassicalOutputs thetaY) (hclassicalZ : RRClassicalOutputs thetaZ) :
    ∃ rate : ℝ, RRPrivateRate thetaY thetaZ rate ∧
      (rate : EReal) = rrPrivateInformation thetaY thetaZ ∧
      ∃ k : ℕ, ∃ p : RRDistribution (Fin (k + 1)),
        ∃ enc : Fin (k + 1) → RRDistribution X,
          rate = rrConditionalEntropy (rrCqState p.prob (rrPreprocess thetaZ enc)) -
            rrConditionalEntropy (rrCqState p.prob (rrPreprocess thetaY enc)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
