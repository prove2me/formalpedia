-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P94_binaryConditionalEntropy_S7
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P94.binaryConditionalEntropy_S7
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:34:03.740211+00:00
-- url     : https://prove2.me/theorems/01046812-f6b1-4b0c-8795-e0af95d75380
-- title:
--   Binary conditional entropy is bounded by the entropy of the error
-- statement:
--   Let $A$ and $B$ be binary random variables with any normalized joint probability law. Let $Q=\Pr[A
--   e B]$, and let $h(t)=-t\log_2 t-(1-t)\log_2(1-t)$, with $0\log_2 0=0$. Then
--
--   $$H(B\mid A)\le h(Q).$$
--
--   The entropy is measured in bits, and a zero-probability conditioning event has weight zero. This bound converts observed binary disagreement probabilities into conditional-entropy upper bounds for the steering inequalities.
-- source:
--   One-sided Device-Independent Quantum Key Distribution: Security, feasibility, and the connection with steering, arXiv:1109.1435v3, PDF p. 6, Eq. (S7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P94

open MeasureTheory

open scoped ComplexConjugate

/-- arXiv:1109.1435v3, PDF p.6, (S7): for every normalized joint binary law,
H(B|A) <= h(Pr[A != B]), including zero-mass conditioning events. -/
theorem binaryConditionalEntropy_S7 (P : Bool → Bool → ℝ)
    (hNonneg : ∀ a b, 0 ≤ P a b)
    (hTotal : ∑ a : Bool, ∑ b : Bool, P a b = 1) :
    conditionalEntropyBits P ≤ QAlgorithms.binEntropy2 (binaryError P) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P94

end
