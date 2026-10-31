-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_reliability_expurgation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.reliability_expurgation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:59:00.129006+00:00
-- url     : https://prove2.me/theorems/fb365282-4eb3-4af8-be43-4bc342424578
-- title:
--   Reliability-only half-size expurgation
-- statement:
--   Let a fixed code on a finite nonempty message set $M$ have messagewise decoding errors $e(m)$, and let $\varepsilon\ge0$. If its uniform average error is at most $\varepsilon/2$, there is a nonempty subset $M_*\subseteq M$ and a normalized decoder for the restricted encoder such that
--
--   $$
--   |M_*|\ge|M|/2,\qquad e_*(m)\le\varepsilon\quad(m\in M_*).
--   $$
--
--   This is the reliability-only variant of expurgation and does not impose secrecy.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 3, Remark 1: reliability-only expurgation

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

/-- Remark 1, PDF p.3. Reliability alone needs average error <= epsilon/2,
with the same half-size conclusion as Lemma 1. -/
theorem reliability_expurgation [Nonempty X] [Nonempty Y] [Nonempty M]
    (theta : X → Matrix Y Y ℂ) (hTheta : RRIsCq theta) (code : RRCode M X Y)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (herror : (Fintype.card M : ℝ)⁻¹ * ∑ m, rrCodeError theta code m ≤ epsilon / 2) :
    ∃ s : Finset M, s.Nonempty ∧ (Fintype.card M : ℝ) / 2 ≤ s.card ∧
      ∃ restricted : RRCode {m : M // m ∈ s} X Y,
        (∀ m, restricted.encoder m = code.encoder m.val) ∧
        RRPublicGood theta restricted epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
