-- Prove2me | Theorems.Thm_RiskSharingProjects_TimeDependent_theorem_6_asymmetry_shortens_duration_iff
-- name    : RiskSharingProjects.TimeDependent.theorem_6_asymmetry_shortens_duration_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:30:49.240851+00:00
-- url     : https://prove2.me/theorems/50323f70-fd03-4bbe-9f8c-b1b4a6976f51
-- title:
--   Theorem 6: information asymmetry shortens the project's duration iff $p^1_1<s_1<p^2_1$, $s_0<p^1_0<p^2_0$ and $s_1<p^1_1q^l_0+p^2_1q^h_0$
-- statement:
--   Consider the basic model with time-dependent cost: the supplier, with saving $s_1$ and penalty shares $p^1_1,p^2_1$, acts first; the manufacturer, with saving $s_0$ and shares $p^1_0,p^2_0$, observes the supplier's action and acts second. Assume Condition 2, and assume $s_1>0$ or $p^2_1\ge0$. Under information symmetry the outcome is an SPNE of this game. Under information asymmetry the supplier holds a belief $\mu$ about the manufacturer's type as in Assumption 2, with class probabilities $q^l_0,q^m_0,q^h_0$, chooses an action maximizing its expected payoff, and the manufacturer best-responds. Then information asymmetry shortens the project's duration relative to information symmetry if and only if
--
--   $$
--   p^1_1<s_1<p^2_1,\qquad s_0<p^1_0<p^2_0,\qquad s_1<p^1_1q^l_0+p^2_1q^h_0 .
--   $$
--
--   Contrary to the common view that information asymmetry worsens project performance, a supplier that is uncertain whether delaying will trigger a costly second period of delay may keep to schedule, which it would not do with full information.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
--
--   Differences from the source:
--
--   - reading: the equilibrium (taken unique; a Pareto or strong equilibrium is reported when it is not, p. 10) → equilibria as sets of outcomes (symmetricSPNEOutcomes, asymmetricOutcomes); AsymmetryShortensDuration = every asymmetric outcome has strictly fewer delay periods than every symmetric outcome; reason: in the strict cases both sets are singletons and this is the paper's comparison; with Theorem 5's tie rule (keep at s1 = p^1_1 q^l_0 + p^2_1 q^h_0) Theorem 6 is false at the tie (s1 = 2, p^1_1 = 1, p^2_1 = 3, s0 = 0, p^1_0 = 2, p^2_0 = 3, q^l_0 = q^h_0 = 1/2: symmetric [D,K], asymmetric [K,K]); the proof of Theorem 6 is silent at equality
--   - reading: the model's sign conventions (p. 7): delaying a task saves direct cost s_i (direct cost decreasing in the task duration), and delay penalties are costs (indirect cost increasing in the project's duration) → hypothesis 0 < s1 ∨ 0 ≤ p21; reason: each disjunct is one of the conventions, so the hypothesis holds in the paper's model; when both fail the equivalence is false (s1 = −3/2, p^1_1 = −5, p^2_1 = −2, s0 = −1, p^1_0 = 5, p^2_0 = 7, q^m_0 = 1: asymmetry shortens [D,K] to [K,K] although s1 < p^2_1 fails)
--   - generalization: the supplier's belief: probabilities q^l_0, q^m_0, q^h_0 of the three classes of Assumption 2 (p. 16) → any probability measure μ on manufacturer types (s0', p^1_0', p^2_0') with full mass on the three classes; q^l_0, q^m_0, q^h_0 are its class masses qLow μ, qMedium μ, qHigh μ; reason: Harsanyi's random type (p. 15); a belief with the given class probabilities, e.g. on three types one from each class, is a special case
--   - generalization: the manufacturer's true cost structure, one of Assumption 2's three classes → any (s0, p^1_0, p^2_0) satisfying Condition 2, including s0 = p^1_0 and s0 = p^2_0; reason: the equivalence holds for these too; specializes to the paper's types
--   - encoding: Assumption 1(b) (p. 10), the sequential game and its SPNE (p. 10), payoffs of Figure 5b (Appendix p. 1) → Action = keep/delay, projectDelay = number of delays, supplierPayoff and manufacturerPayoff from Figure 5b, symmetricSPNEOutcomes = outcomes of pure-strategy SPNEs; reason: this is the model of the theorem; same instances
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Theorem 6, p. 17; proof Appendix p. 5 (PDF 37); Condition 2, p. 12; Assumption 2, p. 16

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_SupplierBelief
import Definitions.Def_RiskSharingProjects_TimeDependent_qLow
import Definitions.Def_RiskSharingProjects_TimeDependent_qHigh
import Definitions.Def_RiskSharingProjects_TimeDependent_AsymmetryShortensDuration
import Definitions.Def_RiskSharingProjects_TimeDependent_Condition2

namespace RiskSharingProjects.TimeDependent

/-- **Theorem 6: information asymmetry shortens the project's duration iff
p^1_1 < s1 < p^2_1, s0 < p^1_0 < p^2_0 and s1 < p^1_1 q^l_0 + p^2_1 q^h_0.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Theorem 6, p. 17 (PDF 17); proof Appendix p. 5 (PDF 37): "For the basic model with
time-dependent cost, information asymmetry shortens the project's duration relative to
information symmetry if and only if p^1_1 < s1 < p^2_1, s0 < p^1_0 < p^2_0, and
s1 < p^1_1 q^l_0 + p^2_1 q^h_0."

Standing assumptions: Condition 2 (p. 12) on the supplier's `s1, p11, p21` and the true
manufacturer's `s0, p10, p20`; Assumption 2 (p. 16) on the supplier's belief `μ` about the
manufacturer's type, with class masses `q^l_0 = qLow μ`, `q^h_0 = qHigh μ`. Under information
symmetry the outcome is an SPNE of the sequential game (Theorem 2); under asymmetry the supplier
maximizes its expected payoff under `μ` and the actual manufacturer best-responds.

**Formalization Note.** Equilibria are sets of outcomes and "shortens" means every asymmetric
equilibrium outcome has strictly fewer periods of project delay than every symmetric SPNE
outcome (`AsymmetryShortensDuration`); at the threshold `s1 = p^1_1 q^l_0 + p^2_1 q^h_0` the
supplier is indifferent and asymmetry does not shorten the duration. The belief `μ` is a general
probability measure on manufacturer types concentrated on Assumption 2's three classes. The true
type `(s0, p10, p20)` is restricted only by Condition 2. The sign hypothesis
`0 < s1 ∨ 0 ≤ p21` holds under either of the model's conventions (p. 7): delaying saves direct
cost (`0 < s1`), or the supplier's penalty share is a cost (`0 ≤ p21`); the equivalence fails when
both are violated. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
theorem theorem_6_asymmetry_shortens_duration_iff (s1 s0 p11 p21 p10 p20 : ℝ)
    (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ)
    (hC2 : Condition2 s1 s0 p11 p21 p10 p20) (hsign : 0 < s1 ∨ 0 ≤ p21) :
    AsymmetryShortensDuration μ s1 p11 p21 s0 p10 p20 ↔
      (p11 < s1 ∧ s1 < p21) ∧ (s0 < p10 ∧ p10 < p20) ∧
        s1 < p11 * qLow μ + p21 * qHigh μ := by sorry

end RiskSharingProjects.TimeDependent
