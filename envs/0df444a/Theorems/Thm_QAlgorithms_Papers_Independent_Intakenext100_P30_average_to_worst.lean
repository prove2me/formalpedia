-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_average_to_worst
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.average_to_worst
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:58:17.077102+00:00
-- url     : https://prove2.me/theorems/c72fa1f7-bbc6-416c-bbc3-4ed01e7d632e
-- title:
--   Expurgation from average reliability and secrecy to messagewise guarantees
-- statement:
--   Fix a code on a finite nonempty message alphabet $M$ and a single normalized eavesdropper reference $\sigma_Z$. Write $e(m)$ for the decoding error and $s(m)=\tfrac12\|\rho_Z^m-\sigma_Z\|_1$ for secrecy error. If $\varepsilon\ge0$ and the uniform-message averages of both errors are at most $\varepsilon/4$, there is a nonempty subset $M_*\subseteq M$ and a code obtained by restricting the same encoder and changing the decoder such that
--
--   $$
--   |M_*|\ge |M|/2,\qquad e_*(m)\le\varepsilon,\qquad \tfrac12\|\rho_Z^m-\sigma_Z\|_1\le\varepsilon\quad(m\in M_*).
--   $$
--
--   The reference $\sigma_Z$ remains the original one. This converts uniform-average guarantees into messagewise guarantees at a loss of at most one bit in message size.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 3, Lemma 1: Average Case to Worst Case Error

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

/-- Lemma 1, PDF p.3. Restrict the original encoder to at least half the
messages, changing only the decoder. Keep the SAME normalized secrecy reference
(footnote 2, p.2). Subset allows equality; epsilon=0 is included. -/
theorem average_to_worst [Nonempty X] [Nonempty Y] [Nonempty Z] [Nonempty M]
    (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (hY : RRIsCq thetaY) (hZ : RRIsCq thetaZ) (code : RRCode M X Y)
    (reference : Matrix Z Z ℂ) (href : IsDensityMatrix reference)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (herror : (Fintype.card M : ℝ)⁻¹ * ∑ m, rrCodeError thetaY code m ≤ epsilon / 4)
    (hleak : (Fintype.card M : ℝ)⁻¹ *
      ∑ m, rrCodeLeak thetaZ code.encoder reference m ≤ epsilon / 4) :
    ∃ s : Finset M, s.Nonempty ∧ (Fintype.card M : ℝ) / 2 ≤ s.card ∧
      ∃ restricted : RRCode {m : M // m ∈ s} X Y,
        (∀ m, restricted.encoder m = code.encoder m.val) ∧
        RRPublicGood thetaY restricted epsilon ∧
        ∀ m, rrCodeLeak thetaZ restricted.encoder reference m ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
