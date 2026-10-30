-- Prove2me | Theorems.Thm_RiskSharingProjects_TimeDependent_theorem_5_supplier_decision
-- name    : RiskSharingProjects.TimeDependent.theorem_5_supplier_decision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:28:24.433945+00:00
-- url     : https://prove2.me/theorems/c888686d-dc09-4605-b70c-3fe84594c4ea
-- title:
--   Theorem 5: the supplier delays iff $s_1\ge p^1_1q^l_0+p^2_1q^h_0$ and keeps iff $s_1\le p^1_1q^l_0+p^2_1q^h_0$
-- statement:
--   Let $\mu$ be a supplier belief (Assumption 2) with class probabilities $q^l_0,q^h_0$, and let $s_1,p^1_1,p^2_1$ be real. Then
--
--   $$
--   D\in\mathcal A^\mu\iff s_1\ge p^1_1q^l_0+p^2_1q^h_0,\qquad K\in\mathcal A^\mu\iff s_1\le p^1_1q^l_0+p^2_1q^h_0 .
--   $$
--
--   So under information asymmetry the supplier's equilibrium decision is *delay* if $s_1>p^1_1q^l_0+p^2_1q^h_0$ and *keep* if $s_1<p^1_1q^l_0+p^2_1q^h_0$; at equality it is indifferent. The threshold shows how the supplier's beliefs about the manufacturer, not only its own costs, drive its decision.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
--
--   Differences from the source:
--
--   - generalization: Cases (a) s1 < p^1_1 < p^2_1 and (b) p^1_1 < s1 < p^2_1 → every real s1, p11, p21; no Condition 2; reason: the characterization does not use the case; specializes to (a) and (b)
--   - reading: "delay" if s1 > p^1_1 q^l_0 + p^2_1 q^h_0; "keep" otherwise → delay is an equilibrium decision iff p11 qLow + p21 qHigh ≤ s1, keep is one iff s1 ≤ p11 qLow + p21 qHigh; reason: decisions are the maximizers of the expected payoff; above the threshold only delay, below only keep, at the threshold the supplier is indifferent and keep is an equilibrium decision as printed (with keep as the only decision, Theorem 6 would be false at the tie)
--   - generalization: the supplier's belief: probabilities q^l_0, q^m_0, q^h_0 of the three classes of Assumption 2 (p. 16) → any probability measure μ on manufacturer types (s0', p^1_0', p^2_0') with full mass on the three classes; q^l_0, q^m_0, q^h_0 are its class masses qLow μ, qMedium μ, qHigh μ; reason: Harsanyi's random type (p. 15); a belief with the given class probabilities, e.g. on three types one from each class, is a special case
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Theorem 5, p. 17; proof Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_SupplierBelief
import Definitions.Def_RiskSharingProjects_TimeDependent_qLow
import Definitions.Def_RiskSharingProjects_TimeDependent_qHigh
import Definitions.Def_RiskSharingProjects_TimeDependent_asymmetricSupplierChoices

namespace RiskSharingProjects.TimeDependent

/-- **Theorem 5: the supplier's equilibrium decision under information asymmetry.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Theorem 5, p. 17 (PDF 17); proof Appendix p. 5 (PDF 37): "In both Cases (a)
s1 < p^1_1 < p^2_1 and (b) p^1_1 < s1 < p^2_1, the supplier's equilibrium decision is "delay" if
s1 > p^1_1 q^l_0 + p^2_1 q^h_0; "keep" otherwise."

For every belief `μ` satisfying Assumption 2 and all real `s1, p11, p21`: `delay` is an
equilibrium decision of the supplier iff `p11 q^l_0 + p21 q^h_0 ≤ s1`, and `keep` is one iff
`s1 ≤ p11 q^l_0 + p21 q^h_0`. Hence the decision is `delay` alone above the threshold, `keep`
alone below it, and both at equality.

**Formalization Note.** Equilibrium decisions are the set of maximizers of the expected payoff
(`asymmetricSupplierChoices`). The characterization holds for every `s1` and without Condition 2,
so Cases (a)/(b) are not imposed. At the threshold the supplier is indifferent and both actions
are equilibrium decisions; the printed "keep otherwise" is the statement that `keep` is an
equilibrium decision there. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
theorem theorem_5_supplier_decision (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ))
    (hμ : SupplierBelief μ) (s1 p11 p21 : ℝ) :
    (Action.delay ∈ asymmetricSupplierChoices μ s1 p11 p21 ↔
        p11 * qLow μ + p21 * qHigh μ ≤ s1) ∧
    (Action.keep ∈ asymmetricSupplierChoices μ s1 p11 p21 ↔
        s1 ≤ p11 * qLow μ + p21 * qHigh μ) := by sorry

end RiskSharingProjects.TimeDependent
