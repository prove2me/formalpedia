-- Prove2me | Theorems.Thm_RiskSharingProjects_TimeDependent_proof_theorem_5_expected_payoffs
-- name    : RiskSharingProjects.TimeDependent.proof_theorem_5_expected_payoffs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:27:19.771752+00:00
-- url     : https://prove2.me/theorems/41b71cfd-9e08-4dd0-8184-dc1e806dc5b3
-- title:
--   Proof of Theorem 5: the supplier's expected payoffs from keep and delay under its belief
-- statement:
--   Let $\mu$ be a supplier belief (Assumption 2) with class probabilities $q^l_0,q^m_0,q^h_0$. For all real $s_1,p^1_1,p^2_1$ the supplier's expected payoffs are
--
--   $$
--   U_1^\mu(K)=-p^1_1\,(q^m_0+q^h_0),\qquad U_1^\mu(D)=(s_1-p^1_1)(q^l_0+q^m_0)+(s_1-p^1_1-p^2_1)\,q^h_0 .
--   $$
--
--   These are the two expressions the supplier compares in Theorem 5: their difference is $s_1-p^1_1q^l_0-p^2_1q^h_0$.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
--
--   Differences from the source:
--
--   - generalization: the supplier's Cases (a) s1 < p^1_1 < p^2_1 and (b) p^1_1 < s1 < p^2_1 → every real s1, p11, p21; no Condition 2; reason: neither formula depends on the case; specializes to (a) and (b)
--   - generalization: the supplier's belief: probabilities q^l_0, q^m_0, q^h_0 of the three classes of Assumption 2 (p. 16) → any probability measure μ on manufacturer types (s0', p^1_0', p^2_0') with full mass on the three classes; q^l_0, q^m_0, q^h_0 are its class masses qLow μ, qMedium μ, qHigh μ; reason: Harsanyi's random type (p. 15); a belief with the given class probabilities, e.g. on three types one from each class, is a special case
--   - encoding: the manufacturer's choice in each class ("will choose keep/delay") → manufacturerResponse, with keep at indifference; reason: it is the unique best response on each class; the tie-break only affects a μ-null set
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), proof of Theorem 5, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_SupplierBelief
import Definitions.Def_RiskSharingProjects_TimeDependent_qLow
import Definitions.Def_RiskSharingProjects_TimeDependent_qMedium
import Definitions.Def_RiskSharingProjects_TimeDependent_qHigh
import Definitions.Def_RiskSharingProjects_TimeDependent_expectedSupplierPayoff

namespace RiskSharingProjects.TimeDependent

/-- **Proof of Theorem 5: the supplier's expected payoffs from keep and delay under its belief.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), proof of Theorem 5, Appendix p. 5 (PDF 37): "In summary, the supplier's expected payoff under
her beliefs is −p^1_1(q^m_0 + q^h_0). If the supplier choose "delay," her expected payoff is
(s1 − p^1_1)(q^l_0 + q^m_0) + (s1 − p^1_1 − p^2_1)q^h_0 by a similar analysis."

For every belief `μ` satisfying Assumption 2 (`SupplierBelief μ`) and all real `s1, p11, p21`,
the expected payoff of `keep` is `−p11 (q^m_0 + q^h_0)` and that of `delay` is
`(s1 − p11)(q^l_0 + q^m_0) + (s1 − p11 − p21) q^h_0`, where `q^l_0, q^m_0, q^h_0` are the
belief's class masses `qLow μ, qMedium μ, qHigh μ`.

**Formalization Note.** The proof is stated for the supplier's Cases (a) s1 < p^1_1 < p^2_1 and
(b) p^1_1 < s1 < p^2_1; the two formulas hold for every `s1, p11, p21`, so no case hypothesis is
imposed. The belief is a general probability measure on manufacturer types. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
theorem proof_theorem_5_expected_payoffs (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ))
    (hμ : SupplierBelief μ) (s1 p11 p21 : ℝ) :
    expectedSupplierPayoff μ s1 p11 p21 Action.keep = -p11 * (qMedium μ + qHigh μ) ∧
    expectedSupplierPayoff μ s1 p11 p21 Action.delay =
      (s1 - p11) * (qLow μ + qMedium μ) + (s1 - p11 - p21) * qHigh μ := by sorry

end RiskSharingProjects.TimeDependent
