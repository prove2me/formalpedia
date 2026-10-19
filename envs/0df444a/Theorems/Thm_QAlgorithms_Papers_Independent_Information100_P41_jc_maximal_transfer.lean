-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P41_jc_maximal_transfer
-- name    : QAlgorithms.Papers.Independent.Information100.P41.jc_maximal_transfer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:32:12.782333+00:00
-- url     : https://prove2.me/theorems/e1fca90c-a217-4c38-b266-f20d8d2d205d
-- title:
--   Attained maximal JC anomaly and saturation of coherence transfer
-- statement:
--   In the resonant ground-atom JC experiment, let $R(\eta,\bar n,\theta)$ be the atomic output obtained by tracing the field from the exact zero/one-excitation evolution of the single-rail density with populations $(1-\bar n,\bar n)$ and real off-diagonal $\eta\sqrt{\bar n(1-\bar n)}$. Write $A(\eta,\bar n,\theta)=\operatorname{Tr}((DR)^{-1}(R-DR)R)$ and $\Delta C(\eta,\bar n,\theta)=C(R)-C(|g\rangle\langle g|)$, where $D$ is energy-basis dephasing and entropy uses natural logs. For fixed $0<\bar n<1$ and $\eta=1$, the angle $\pi/2$ attains the largest anomaly over all real angles with $\sin\theta\ne0$:
--
--   $$\operatorname{Re}A(1,\bar n,\theta)\le\operatorname{Re}A(1,\bar n,\pi/2).$$
--
--   At equal populations,
--
--   $$\Delta C(1,1/2,\pi/2)=\ln2=\ln(1+\operatorname{Re}A(1,1/2,\pi/2)),\qquad A(1,1/2,\pi/2)=1.$$
--
--   This transfer is an attained maximum: every experiment with $0\le\eta,\bar n\le1$ and real $\theta$ has coherence change at most this value. No uniqueness of the maximizing angle is claimed.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, PDF p. 4, Maximum and saturation following Eq.(11)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/-- PDF p.4: attained anomaly maximum at pi/2 for eta=1; equal-population transfer attains
maximal qubit coherence ln 2 and saturates Eq.(6). No uniqueness over real angles is claimed. -/
theorem jc_maximal_transfer (nbar : ℝ) (hnbar : 0 < nbar ∧ nbar < 1) :
    (∀ theta : ℝ, Real.sin theta ≠ 0 →
      (jcAnomaly 1 nbar theta).re ≤ (jcAnomaly 1 nbar (Real.pi / 2)).re) ∧
    jcChange 1 (1 / 2) (Real.pi / 2) = Real.log 2 ∧
    jcAnomaly 1 (1 / 2) (Real.pi / 2) = 1 ∧
    jcChange 1 (1 / 2) (Real.pi / 2) =
      Real.log (1 + (jcAnomaly 1 (1 / 2) (Real.pi / 2)).re) ∧
    (∀ eta b theta : ℝ, (0 ≤ eta ∧ eta ≤ 1) → (0 ≤ b ∧ b ≤ 1) →
      jcChange eta b theta ≤ jcChange 1 (1 / 2) (Real.pi / 2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P41

end
