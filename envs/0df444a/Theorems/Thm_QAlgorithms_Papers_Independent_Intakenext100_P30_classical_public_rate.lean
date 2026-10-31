-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_classical_public_rate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.classical_public_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:55:50.328697+00:00
-- url     : https://prove2.me/theorems/30ec939a-a2ee-466d-9892-72c288c501e0
-- title:
--   Single-letter public rate for classical outputs
-- statement:
--   Suppose all receiver output states of the fixed cq channel $\Theta$ are simultaneously diagonalizable in one orthonormal basis. The operational public iterated limit exists and satisfies
--
--   $$
--   R_{\rm pub}(\Theta)=\sup_{P_X}\bigl[H(X)-H(X|Y)\bigr].
--   $$
--
--   The rate means $\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}C_{\rm pub}^{\varepsilon}(\Theta^{\otimes n})/n$, with existence asserted. Only reliability is required. This recovers the classical single-letter public formula.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
--
--   The maximum is attained: there exists a normalized input law $P_X$ whose displayed mutual information equals the operational rate.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 5, §IV (18): classical single-letter public rate

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

/-- Section IV, PDF p.5, (18): classical-output single-letter public rate.
The receiver states have a common diagonalizing basis; secrecy is not imposed.
An optimizing input law is a conclusion, retaining the printed maximum. -/
theorem classical_public_rate [Nonempty X] [Nonempty Y]
    (theta : X → Matrix Y Y ℂ) (hTheta : RRIsCq theta) (hclassical : RRClassicalOutputs theta) :
    ∃ rate : ℝ, RRPublicRate theta rate ∧ (rate : EReal) = rrPublicInformation theta ∧
      ∃ p : RRDistribution X,
        rate = vnEntropy (Matrix.diagonal (fun x => (p.prob x : ℂ))) -
          rrConditionalEntropy (rrCqState p.prob theta) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
