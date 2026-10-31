-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_bob_pairing_penalty
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.bob_pairing_penalty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:37:10.90832+00:00
-- url     : https://prove2.me/theorems/6cbdcd0a-9686-45c5-8103-1113a92a8319
-- title:
--   Bob-chosen modified-COW pairings halve the rate
-- statement:
--   In the paper’s balanced, independent companion-pulse model, let $P(a,b)$ be the normalized joint law of candidate raw bits, with both bit marginals uniform. Bob’s companion choice accepts half the candidates independently of these bit values. For the constructed acceptance law $P(a,b,c)=P(a,b)/2$, where $c$ is the acceptance flag,
--
--   $$\Pr(c=1)=\frac12,\qquad P(a,b\mid c=1)=P(a,b).$$
--
--   For $\mu\ge0$, $Q\in[0,1]$, and Alice/Bob Holevo quantities $\chi_A,\chi_B$, the signed expression $D(s)=s[1-h(Q)-\min(\chi_A,\chi_B)]$ therefore satisfies
--
--   $$D(\mu/4)=\frac12D(\mu/2).$$
--
--   Multiplication by $t\eta$ gives the source’s per-slot first-order rates. This calculation applies to the specified COWm1/COWm2 pairing model; it is not uniform over arbitrary correlated pairing schedules.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 9, IV E / Appendix A: Bob-chosen pairings cost a factor of two

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- PDF p.9 and Appendix A pp.11–12: Bob's random pairing retains half the
candidate bits, leaves their conditional joint law unchanged, and halves the
COWm1/COWm2 first-order signed rate in this balanced-pulse model. -/
theorem bob_pairing_penalty (P : Bool × Bool → ℝ)
    (hP : (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1)
    (hbalanced : (∀ a, ∑ b, P (a,b) = 1/2) ∧ (∀ b, ∑ a, P (a,b) = 1/2))
    (mu Q ca cb : ℝ)
    (hmu : 0 ≤ mu) (hQ : Q ∈ Set.Icc (0:ℝ) 1) :
    (∑ x, bobPairLaw P (x,true)) = 1/2 ∧
    (∀ x, bobPairLaw P (x,true) / (∑ y, bobPairLaw P (y,true)) = P x) ∧
    dw (mu/4) Q ca cb = dw (mu/2) Q ca cb / 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
