-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P41_jc_output_population_coherence
-- name    : QAlgorithms.Papers.Independent.Information100.P41.jc_output_population_coherence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:26:09.573718+00:00
-- url     : https://prove2.me/theorems/3018fa3c-eb16-4a79-b9a9-166c66c77ed1
-- title:
--   Ground-atom JC population and coherence amplitude
-- statement:
--   Consider resonant Jaynes–Cummings evolution in the rotating-wave approximation, with $\hbar=1$ and $\theta=gt$. The atom starts in $|g\rangle$, and the field has single-rail density matrix $F=\begin{pmatrix}1-\bar n&\eta\sqrt{\bar n(1-\bar n)}\\\eta\sqrt{\bar n(1-\bar n)}&\bar n\end{pmatrix}$, where $0\le\bar n,\eta\le1$. Define $V_\theta|0\rangle=|g,0\rangle$ and $V_\theta|1\rangle=\cos\theta|g,1\rangle-i\sin\theta|e,0\rangle$, and let $R=\operatorname{Tr}_{F}(V_\theta F V_\theta^\dagger)$. For $0\le\theta\le\pi/2$,
--
--   $$p_e=R_{ee}=\bar n\sin^2\theta,\qquad |R_{ge}|=\eta\sqrt{\bar n(1-\bar n)}\sin\theta.$$
--
--   These formulas quantify population transfer and coherence transfer from the field to the atom.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, PDF p. 4, Following Eq.(10)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/-- PDF p.4, following Eq.(10): population and unsigned coherence amplitude on the positive-sine branch. -/
theorem jc_output_population_coherence (eta nbar theta : ℝ)
    (heta : 0 ≤ eta ∧ eta ≤ 1) (hnbar : 0 ≤ nbar ∧ nbar ≤ 1)
    (htheta : 0 ≤ theta ∧ theta ≤ Real.pi / 2) :
    (jcOutput eta nbar theta 1 1).re = nbar * Real.sin theta ^ 2 ∧
    ‖jcOutput eta nbar theta 0 1‖ = eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta := by sorry

end QAlgorithms.Papers.Independent.Information100.P41

end
