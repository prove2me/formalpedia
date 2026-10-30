-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P36_entropySubentropyGap
-- name    : QAlgorithms.Papers.Independent.Bridge50.P36.entropySubentropyGap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:18:04.84271+00:00
-- url     : https://prove2.me/theorems/00ca4ac0-0b51-427d-8f9d-25e8eea47915
-- title:
--   Entropy–subentropy gap with the printed harmonic bound
-- statement:
--   Let $\rho$ be a positive semidefinite trace-one state on a register of dimension $d\ge1$. Let $H(\rho)$ be its von Neumann entropy in bits and $Q(\rho)$ its standard subentropy in bits. Set $H_d=\sum_{t=1}^{d}1/t$. Then
--
--   $$
--   H(\rho)-Q(\rho)\le H_d\log_2 e.
--   $$
--
--   Standard subentropy is the mean Shannon entropy of a computational-basis measurement after a Haar-distributed unitary, minus $(\sum_{t=2}^{d}1/t)\log_2 e$. This uses the normalized definition of subentropy, correcting the offset in the preceding printed identity (A1), while retaining the printed, looser inequality (A2).
--
--   This bounds the difference between entropy and subentropy in a dimension-dependent way. Subentropy here is a state quantity, distinct from channel coherent information $Q^{(1)}$.
-- source:
--   Superadditivity of private information for any number of uses of the channel, arXiv:1502.05326v1, PDF p. 5, Appendix A, (A2)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P36

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory

-- These imports are pinned accepted libraries, permitted by the repair task.
-- P08.Ensemble allows an impossible zero-sized normalized ensemble; its total=1
-- field excludes that case without a separate positive-size field.

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel maximumCoherentInformation dilationPower erasureDilation)

open QAlgorithms.Papers.Independent.Dependency50.P07 (accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P48 (privateMaximum)

variable {A B E C D : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D]

/-- Appendix A, PDF p.5 (A2), continued p.6: printed entropy–subentropy
gap bound, including the t=1 term in H_d. Standard subentropy uses the
corrected (A1) offset; the looser printed (A2) bound is retained unchanged. -/
theorem entropySubentropyGap (d : ℕ) (hd : 0 < d)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho) :
    vnEntropy rho - subentropy rho ≤ harmonicValue d * Real.logb 2 (Real.exp 1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P36

end
