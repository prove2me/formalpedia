-- Prove2me | Theorems.Thm_RiskSharingProjects_TimeDependent_lemma_2_dominant_strategy
-- name    : RiskSharingProjects.TimeDependent.lemma_2_dominant_strategy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:25:20.424276+00:00
-- url     : https://prove2.me/theorems/fe623945-a47f-445f-8e40-e063b12f8206
-- title:
--   Lemma 2 (Dominant Strategy): keep dominates if $s_0<p^1_0$, delay if $s_0>p^2_0$; the supplier delays if $p^1_1<p^2_1<s_1$
-- statement:
--   Assume Condition 2. Then:
--
--   1. if $s_0<p^1_0$, the manufacturer's only best response to either action of the supplier is *keep*: $\mathrm{BR}_0(K)=\mathrm{BR}_0(D)=\{K\}$;
--   2. if $s_0>p^2_0$, its only best response to either action is *delay*: $\mathrm{BR}_0(K)=\mathrm{BR}_0(D)=\{D\}$;
--   3. if $s_1>0$ and $p^1_1<p^2_1<s_1$, then *delay* is strictly better than *keep* for the supplier against any manufacturer that best-responds: for every manufacturer type $\theta=(s_0',p^{1\prime}_0,p^{2\prime}_0)$ with $p^{1\prime}_0<p^{2\prime}_0$ and every strategy $\sigma$ with $\sigma(a)\in\mathrm{BR}_0^\theta(a)$ for both $a$,
--
--   $$
--   u_1\big(K,\sigma(K)\big)<u_1\big(D,\sigma(D)\big).
--   $$
--
--   The lemma identifies when a firm's decision does not depend on what it knows about the other, which is what makes information asymmetry irrelevant outside the cases of Theorem 5.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
--
--   Differences from the source:
--
--   - reading: "delay" is the dominant strategy for the supplier → delay is strictly better than keep against every strategy of a manufacturer type that best-responds after each supplier action; reason: the proof (Appendix p. 2) compares the supplier's payoffs against the manufacturer's optimal responses; against all four manufacturer strategies the claim is false (σ = keep after keep, delay after delay gives keep 0 and delay s1 − p^1_1 − p^2_1 < 0 when s1 < p^1_1 + p^2_1, e.g. p^1_1 = 1, p^2_1 = 2, s1 = 5/2)
--   - generalization: the true manufacturer, in the proof's three cases s0 < p^1_0 < p^2_0, p^1_0 < s0 < p^2_0, p^1_0 < p^2_0 < s0 → every manufacturer type θ with p^1_0' < p^2_0', including s0' = p^1_0' and s0' = p^2_0'; reason: specializes to the true type, which has p^1_0 < p^2_0 by Condition 2
--   - reading: positive saving from delay, used in the proof ("the supplier chooses delay since 0 < s1") → hypothesis 0 < s1 in clause 3; reason: the direct cost is decreasing in the task duration (p. 7); without it clause 3 fails (p^1_1 = −5, p^2_1 = −2, s1 = −1, s0 = −1, p^1_0 = 5, p^2_0 = 7 satisfy Condition 2, and against the type (1, 0, 2) keep pays 5 and delay 4)
--   - encoding: "keep" ("delay") is the dominant strategy for the manufacturer → the manufacturer's best-response set after each supplier action is {keep} ({delay}); reason: the manufacturer moves last, so a dominant action is its unique optimal choice at both of its decision nodes
--   - generalization: the model's sign conventions (p. 7: savings s_i > 0 since the direct cost is decreasing in the task duration; penalty shares are costs), standing throughout the paper → not assumed in clauses 1 and 2; clause 3 carries only 0 < s1; reason: clauses 1 and 2 follow from Condition 2 alone; specializes to the paper's model, where the conventions hold
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Lemma 2, p. 12; proof Appendix pp. 1-2 (PDF 33-34)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_supplierPayoff
import Definitions.Def_RiskSharingProjects_TimeDependent_manufacturerBestResponses
import Definitions.Def_RiskSharingProjects_TimeDependent_Condition2

namespace RiskSharingProjects.TimeDependent

/-- **Lemma 2 (Dominant Strategy).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Lemma 2, p. 12 (PDF 12); proof Appendix pp. 1–2 (PDF 33–34): "Under Assumption 1(b) and
Condition 2, if s0 < p^1_0, "keep" is the dominant strategy for the manufacturer; if s0 > p^2_0,
"delay" is the dominant strategy for the manufacturer. If p^1_1 < p^2_1 < s1, "delay" is the
dominant strategy for the supplier."

Under `Condition2`:
* (a) if `s0 < p10`, the manufacturer's only best response to either supplier action is `keep`;
* (b) if `p20 < s0`, it is `delay`;
* (c) if `0 < s1` and `p11 < p21 < s1`, then against every manufacturer type `θ` with
  `θ.2.1 < θ.2.2` (first-period penalty share below the second, as in Condition 2) and every
  strategy `σ` of that type that best-responds after each supplier action, the supplier's payoff
  from `delay` is strictly larger than from `keep`.

**Formalization Note.** "Dominant strategy for the supplier" is read as in the proof (Appendix
p. 2): delay beats keep against the manufacturer's optimal responses, for every manufacturer
cost structure; against arbitrary manufacturer strategies it would be false. `0 < s1` is the
model's convention that delaying a task saves direct cost (p. 7: the direct cost is "decreasing
in the task duration"); the proof's "the supplier chooses "delay" since 0 < s1" uses it. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
theorem lemma_2_dominant_strategy (s1 s0 p11 p21 p10 p20 : ℝ)
    (hC2 : Condition2 s1 s0 p11 p21 p10 p20) :
    (s0 < p10 → ∀ a1, manufacturerBestResponses s0 p10 p20 a1 = {Action.keep}) ∧
    (p20 < s0 → ∀ a1, manufacturerBestResponses s0 p10 p20 a1 = {Action.delay}) ∧
    (0 < s1 → p11 < p21 → p21 < s1 →
      ∀ θ : ℝ × ℝ × ℝ, θ.2.1 < θ.2.2 → ∀ σ : Action → Action,
        (∀ a, σ a ∈ manufacturerBestResponses θ.1 θ.2.1 θ.2.2 a) →
        supplierPayoff s1 p11 p21 Action.keep (σ Action.keep) <
          supplierPayoff s1 p11 p21 Action.delay (σ Action.delay)) := by sorry

end RiskSharingProjects.TimeDependent
