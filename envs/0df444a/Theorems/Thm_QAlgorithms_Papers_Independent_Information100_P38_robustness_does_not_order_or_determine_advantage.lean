-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_robustness_does_not_order_or_determine_advantage
-- name    : QAlgorithms.Papers.Independent.Information100.P38.robustness_does_not_order_or_determine_advantage
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:09:59.131129+00:00
-- url     : https://prove2.me/theorems/04757401-0b6f-463d-95a8-7bd9bd1f55f5
-- title:
--   Remark 2
-- statement:
--   Fix $H=E|1\rangle\langle1|$ with $E>0$. For $j=1,2,3$, let $M_j$ be binary with first effect $(I+\mathbf m_j\cdot\boldsymbol\sigma)/2$ and second effect its complement, where $\mathbf m_1=(3/5,0,4/5)$, $\mathbf m_2=(7/10,0,0)$, and $\mathbf m_3=(3/5,0,0)$. All are POVMs, and
--
--   $$\begin{aligned} (R_C(M_1),A_H^{M_1})&=(3/5,3E/10),\\(R_C(M_2),A_H^{M_2})&=(7/10,49E/200),\\(R_C(M_3),A_H^{M_3})&=(3/5,9E/50).\end{aligned}$$
--
--   Consequently $R_C(M_1)<R_C(M_2)$ while $A_H^{M_1}>A_H^{M_2}$, and $R_C(M_1)=R_C(M_3)$ while $A_H^{M_1}\ne A_H^{M_3}$. These are respectively failures of ordering and of determination by robustness.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 9, Remark 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.9, Remark 2: BOTH explicit counterexamples, with all robustness and
advantage constants, show failure of ordering and failure of determination. -/
theorem robustness_does_not_order_or_determine_advantage (E : ℝ) (hE : 0 < E) :
    let M1 := ergotropicBlochMeasurement ![3/5, 0, 4/5]
    let M2 := ergotropicBlochMeasurement ![7/10, 0, 0]
    let M3 := ergotropicBlochMeasurement ![3/5, 0, 0]
    IsPOVM M1 ∧ IsPOVM M2 ∧ IsPOVM M3 ∧
    measurementCoherenceRobustness M1 = 3/5 ∧ measurementCoherenceRobustness M2 = 7/10 ∧
    measurementCoherenceRobustness M3 = 3/5 ∧
    observationalAdvantage ![0, E] M1 = 3*E/10 ∧
    observationalAdvantage ![0, E] M2 = 49*E/200 ∧
    observationalAdvantage ![0, E] M3 = 9*E/50 ∧
    measurementCoherenceRobustness M1 < measurementCoherenceRobustness M2 ∧
    observationalAdvantage ![0, E] M2 < observationalAdvantage ![0, E] M1 ∧
    measurementCoherenceRobustness M1 = measurementCoherenceRobustness M3 ∧
    observationalAdvantage ![0, E] M1 ≠ observationalAdvantage ![0, E] M3 := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
