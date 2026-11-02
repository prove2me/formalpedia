-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P94_postselectedSteering_S10
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P94.postselectedSteering_S10
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:33:33.361203+00:00
-- url     : https://prove2.me/theorems/0b504226-e115-439d-aecb-b82d77bdd7ce
-- title:
--   Two-basis postselected steering inequality
-- statement:
--   Consider a normalized local-hidden-state model for binary Alice outputs and a public detection flag, with a predetermined no-click bit, and Bob's two mutually unbiased projective qubit measurements. The same hidden ensemble must reproduce every setting pair. Assume the two Alice settings have the same detection probability $\eta_A$. When $\eta_A>0$, let $Q_i^{\rm ps}=\Pr[A_i
--   e B_i\mid s_i=1]$ for setting $i$, and let $h$ denote binary entropy in bits. Then
--
--   $$\eta_A\bigl[2-h(Q_1^{\rm ps})-h(Q_2^{\rm ps})\bigr]\le1.$$
--
--   At $\eta_A=0$, interpret both weighted entropy terms as zero, giving $0\le1$. In particular, perfect detected correlations can violate this criterion only above efficiency $1/2$. The statement is a necessary constraint on local-hidden-state correlations; it does not assert sufficiency for key security.
-- source:
--   One-sided Device-Independent Quantum Key Distribution: Security, feasibility, and the connection with steering, arXiv:1109.1435v3, PDF p. 6, Eq. (S10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P94

open MeasureTheory

open scoped ComplexConjugate

/-- arXiv:1109.1435v3, PDF p.6, (S10): two-basis postselected steering inequality
for mutually unbiased qubit measurements and a common detection probability.
For positive eta_A this is eta_A*(2-h(Q_1^ps)-h(Q_2^ps))<=1.
The weighted form includes the zero-efficiency branch. No entropy tightness is assumed. -/
theorem postselectedSteering_S10 {Lambda : Type*} [MeasurableSpace Lambda]
    (U : BobBases) (L : HiddenModel Lambda U) (hMUB : MutuallyUnbiased U)
    (hCommonEfficiency : detectionProbability L false = detectionProbability L true) :
    2 * detectionProbability L false - weightedDetectedEntropy L false -
      weightedDetectedEntropy L true ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P94

end
