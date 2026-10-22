-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_interceptResend
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.interceptResend
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:38:45.649002+00:00
-- url     : https://prove2.me/theorems/ea3db356-a52e-44d0-9f08-cca25d17ccd9
-- title:
--   I.B.5: intercept-resend information and disturbance
-- statement:
--   Let Alice's BB84 bit and all basis choices be uniform and independent. Eve independently intercepts a fraction $p\in[0,1]$ of signals, measures in a random BB84 basis and resends her outcome. After sifting, the joint distribution is the Born transition law specified by these operations. Its error rate $Q$ and both classical mutual informations, in bits, satisfy
--
--   $$Q=p/4,\qquad I(A:E)=I(B:E)=p/2=2Q.$$
--
--   The joint law is nonnegative and normalized. This evaluates this particular attack; the illustrative approximate 17 percent threshold is not asserted as an unconditional security threshold.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 5, I.B.5: intercept-resend information and disturbance

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- I.B.5, PDF p.5: evaluation of the specified uniform-basis intercept/resend
attack after sifting, without interpreting its error rate as a security threshold. -/
theorem interceptResend (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a b e, 0 ≤ irLaw p a b e) ∧
    (∑ a : Bool, ∑ b : Bool, ∑ e : IRRecord, irLaw p a b e) = 1 ∧
    irError p = p/4 ∧ classicalMI (irAE p) = p/2 ∧
    classicalMI (irBE p) = p/2 ∧ p/2 = 2*irError p := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
