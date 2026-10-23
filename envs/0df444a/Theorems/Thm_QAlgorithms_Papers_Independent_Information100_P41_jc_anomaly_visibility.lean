-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P41_jc_anomaly_visibility
-- name    : QAlgorithms.Papers.Independent.Information100.P41.jc_anomaly_visibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:26:48.69669+00:00
-- url     : https://prove2.me/theorems/88d6373a-4ab7-4c3d-92a5-99cecc680b61
-- title:
--   JC trace anomaly equals squared coherence visibility
-- statement:
--   In the resonant ground-atom JC experiment, let $0<\bar n<1$, $0\le\eta\le1$, and $\sin\theta\ne0$. The field density is $F=\begin{pmatrix}1-\bar n&\eta\sqrt{\bar n(1-\bar n)}\\\eta\sqrt{\bar n(1-\bar n)}&\bar n\end{pmatrix}$. Let $R=\operatorname{Tr}_{F}(V_\theta F V_\theta^\dagger)$ with $V_\theta|0\rangle=|g,0\rangle$ and $V_\theta|1\rangle=\cos\theta|g,1\rangle-i\sin\theta|e,0\rangle$. The reference output equals $R$ because the ground atomic input is incoherent. With energy-basis dephasing $D$, $p_g=R_{gg}$ and $p_e=R_{ee}$, the computed anomaly satisfies
--
--   $$A_C=\operatorname{Tr}((DR)^{-1}(R-DR)R)=\frac{\eta^2(1-\bar n)}{1-\bar n\sin^2\theta}=\frac{|R_{ge}|^2}{p_gp_e}.$$
--
--   Both populations are positive on this domain, so the anomaly measures a well-defined squared coherence visibility.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, PDF p. 4, Eq.(11)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/-- PDF p.4, Eq.(11): computed trace anomaly equals squared coherence visibility.
Both output populations are positive; no cancellation at sin(theta)=0 is made. -/
theorem jc_anomaly_visibility (eta nbar theta : ℝ)
    (heta : 0 ≤ eta ∧ eta ≤ 1) (hnbar : 0 < nbar ∧ nbar < 1)
    (htheta : Real.sin theta ≠ 0) :
    jcAnomaly eta nbar theta =
      ((eta ^ 2 * (1 - nbar) / (1 - nbar * Real.sin theta ^ 2) : ℝ) : ℂ) ∧
    jcAnomaly eta nbar theta =
      ((‖jcOutput eta nbar theta 0 1‖ ^ 2 /
        ((jcOutput eta nbar theta 0 0).re * (jcOutput eta nbar theta 1 1).re) : ℝ) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Information100.P41

end
