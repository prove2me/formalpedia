-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P94_lossTolerantSteering_S1
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P94.lossTolerantSteering_S1
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:32:26.298521+00:00
-- url     : https://prove2.me/theorems/036e8d87-6c75-47bc-b872-b975c021f110
-- title:
--   Loss-tolerant steering inequality with a public detection flag
-- statement:
--   Let Bob's two binary qubit projective measurements have orthonormal bases $\{u_{1a}\}$ and $\{u_{2b}\}$, with $a,b\in\{0,1\}$. Define $q=-\log_2\max_{a,b}|\langle u_{1a},u_{2b}\rangle|^2$. Suppose the observed probabilities $P(a,s,b\mid i,j)$ admit a single normalized local-hidden-state ensemble for all setting pairs: Alice's response can depend on $i$ and the hidden variable, and Bob measures the associated normalized qubit state in basis $j$. Here $s=1$ means Alice detects, and her outcome at $s=0$ is predetermined.
--
--   Assume Alice's detection probability is the same, $\eta_A$, at both settings. Let $Q_2=\Pr[A_2
--   e B_2]$ use all outputs, including no-click assignments. Write $W_i=\eta_A h(Q_i^{\rm ps})$ when $\eta_A>0$, where $Q_i^{\rm ps}=\Pr[A_i
--   e B_i\mid s=1]$; set $W_i=0$ at $\eta_A=0$. The binary entropy $h$ is in bits. Then
--
--   $$q\le W_1+h(Q_2)+(1-\eta_A).$$
--
--   At zero efficiency, $q\le1$. Violation excludes a local-hidden-state description. This is the steering inequality corresponding algebraically to the nonpositive right-hand side of Eq. (8); no operational key-security implication is asserted by this item.
-- source:
--   One-sided Device-Independent Quantum Key Distribution: Security, feasibility, and the connection with steering, arXiv:1109.1435v3, PDF p. 6, Eq. (S1), derived from (S2)–(S9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P94

open MeasureTheory

open scoped ComplexConjugate

/-- arXiv:1109.1435v3, PDF pp.3,6, (S1): loss-tolerant steering inequality.
The printed eta is eta_A from (S6)--(S9). The weighted form includes eta_A=0;
the additional zero branch spells out q<=1 without an undefined postselected error. -/
theorem lossTolerantSteering_S1 {Lambda : Type*} [MeasurableSpace Lambda]
    (U : BobBases) (L : HiddenModel Lambda U)
    (hCommonEfficiency : detectionProbability L false = detectionProbability L true) :
    projectiveOverlapIncompatibility U ≤ weightedDetectedEntropy L false +
      QAlgorithms.binEntropy2 (fullError L true) + (1 - detectionProbability L false) ∧
    (detectionProbability L false = 0 → projectiveOverlapIncompatibility U ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P94

end
