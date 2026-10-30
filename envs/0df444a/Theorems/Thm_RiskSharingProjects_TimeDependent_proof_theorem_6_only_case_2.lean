-- Prove2me | Theorems.Thm_RiskSharingProjects_TimeDependent_proof_theorem_6_only_case_2
-- name    : RiskSharingProjects.TimeDependent.proof_theorem_6_only_case_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:29:10.214981+00:00
-- url     : https://prove2.me/theorems/dd2c11eb-5a4c-4aae-bcf1-7a736a47c1c8
-- title:
--   Proof of Theorem 6: only Case 2 of Theorem 2 can be shortened
-- statement:
--   Assume Condition 2 and let $\mu$ be a supplier belief (Assumption 2). If information asymmetry shortens the project's duration relative to information symmetry, then
--
--   $$
--   p^1_1<s_1\quad\text{and}\quad s_0<p^1_0,
--   $$
--
--   the conditions of Case 2 of Theorem 2. In every other case the supplier's decision under symmetry already keeps the duration as short as asymmetry can make it.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
--
--   Differences from the source:
--
--   - reading: the equilibrium (taken unique; a Pareto or strong equilibrium is reported when it is not, p. 10) → equilibria as sets of outcomes (symmetricSPNEOutcomes, asymmetricOutcomes); AsymmetryShortensDuration = every asymmetric outcome has strictly fewer delay periods than every symmetric outcome; reason: in the strict cases both sets are singletons and this is the paper's comparison; with Theorem 5's tie rule (keep at s1 = p^1_1 q^l_0 + p^2_1 q^h_0) Theorem 6 is false at the tie (s1 = 2, p^1_1 = 1, p^2_1 = 3, s0 = 0, p^1_0 = 2, p^2_0 = 3, q^l_0 = q^h_0 = 1/2: symmetric [D,K], asymmetric [K,K]); the proof of Theorem 6 is silent at equality
--   - reading: "Case 2 of Theorem 2 is the only case when the project's duration can be shortened" → shortening implies p11 < s1 and s0 < p10; reason: Case 2 is the region s1 > p^1_1, s0 < p^1_0 of Theorem 2's table
--   - generalization: the supplier's belief: probabilities q^l_0, q^m_0, q^h_0 of the three classes of Assumption 2 (p. 16) → any probability measure μ on manufacturer types (s0', p^1_0', p^2_0') with full mass on the three classes; q^l_0, q^m_0, q^h_0 are its class masses qLow μ, qMedium μ, qHigh μ; reason: Harsanyi's random type (p. 15); a belief with the given class probabilities, e.g. on three types one from each class, is a special case
--   - generalization: the model's sign conventions (p. 7: savings s_i > 0 since the direct cost is decreasing in the task duration; penalty shares are costs), standing throughout the paper; the true manufacturer type in one of Assumption 2's three classes → no sign hypothesis; the true (s0, p^1_0, p^2_0) is any triple satisfying Condition 2, including s0 = p^1_0 and s0 = p^2_0; reason: the implication holds without them (if s0 ≥ p^1_0, Condition 2 forces 0 < p^1_1 < p^2_1); specializes to the paper's model
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), proof of Theorem 6, Appendix p. 5 (PDF 37)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_SupplierBelief
import Definitions.Def_RiskSharingProjects_TimeDependent_AsymmetryShortensDuration
import Definitions.Def_RiskSharingProjects_TimeDependent_Condition2

namespace RiskSharingProjects.TimeDependent

/-- **Proof of Theorem 6: only Case 2 of Theorem 2 can be shortened.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), proof of Theorem 6, Appendix p. 5 (PDF 37): "We first note that the Case 2 of Theorem 2 is
the only case when the project's duration can be shortened in information asymmetry relative to
information symmetry."

Under Condition 2 and a belief satisfying Assumption 2: if information asymmetry
shortens the project's duration, then `p11 < s1` and `s0 < p10` (the conditions of Case 2 of
Theorem 2).

**Formalization Note.** `AsymmetryShortensDuration` requires every asymmetric equilibrium outcome
to be strictly shorter than every symmetric SPNE outcome. No sign condition on the parameters is
needed beyond Condition 2. The true manufacturer type `(s0, p10, p20)` is arbitrary subject to
Condition 2. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
theorem proof_theorem_6_only_case_2 (s1 s0 p11 p21 p10 p20 : ℝ)
    (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ)
    (hC2 : Condition2 s1 s0 p11 p21 p10 p20) :
    AsymmetryShortensDuration μ s1 p11 p21 s0 p10 p20 → p11 < s1 ∧ s0 < p10 := by sorry

end RiskSharingProjects.TimeDependent
