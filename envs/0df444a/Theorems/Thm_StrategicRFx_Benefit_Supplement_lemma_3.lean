-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_lemma_3
-- name    : StrategicRFx.Benefit.Supplement.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:14:40.9048+00:00
-- url     : https://prove2.me/theorems/ec8ce176-0194-495e-9a5a-abc4d37b43e4
-- title:
--   Lemma 3 — optimal leader keep-quote and follower reduction with future responses
-- statement:
--   Let the reduced bargaining parameters satisfy the standing source hypotheses, and use a buyer selector meeting the source's technical tie construction. Consider an iterative tendering procedure and a public history at which negotiation would contract with supplier $i$ first and reject the other supplier $j$'s offer. Compare responses using final negotiation profits after all future responses, under a sequentially rational continuation profile. Then
--
--   $$\text{keep }\widetilde\pi_i\text{ is an optimal response for }i,\qquad \widetilde\pi_j^{\mathrm{next}}<\widetilde\pi_j\text{ when }j\text{ is requested}.$$
--
--   The first clause asserts existence of a best response keeping the leader's current quote when he is requested; it does not assert uniqueness of his complete strategy. The second applies at the follower's actual response opportunity. Simultaneous requests use the same revealed pair for both decisions. All comparisons concern final payoffs rather than myopic negotiation profits.
--
--   Differences from the source:
--   - encoding: real nonnegative profit quotations and revealed requests → NNReal quotations, full public histories, arbitrary whole-strategy deviations, singleton or simultaneous requests; reason: retains the continuous quote domain and both request variants without a finite horizon
--   - reading: equilibrium and optimal responses considering future play → pure Nash optimality at the initial quotes and at every reachable public history; reason: p. 7 explicitly requires all potential outcomes, including off-path outcomes, to be subgame perfect; ec15–ec16 compare equilibrium future responses
--   - reading: procurement begins after tendering terminates; no transaction has zero profit → endless tendering has no final quote and all three no-transaction profits are explicitly zero; reason: extends p. 7 normalization to the operational boundary where negotiation never begins; the paper assigns no other outcome to a solicitation that never ends, and p. 7 normalizes every no-transaction profit to 0
--   - reading: the leader's optimal response is to keep his current offer → existence of a best response keeping his quote, and strict follower reduction at each requested opportunity; reason: the ec15 proof compares profits weakly, so no uniqueness of the leader strategy is inferred
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Lemma 3, p. 19; proof pp. ec14–ec16

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Tendering

namespace StrategicRFx.Benefit.Supplement

/-- Lemma 3, p. 19; proof ec14–ec16. Optimal responses compare final
negotiation profits under complete, sequentially rational future strategies.
Keeping the leader's quote is an optimal response, not a unique strategy. -/
theorem lemma_3 (P : Params) (hP : Standing P) (β : BuyerSelector)
    (hβ : SourceBuyerSelector P β) (p : TenderProcedure)
    (hp : IterativeTenderProcedure p) (s : TenderProfile)
    (hs : ∀ g, ReachableHistory p g → (continuationGame P β p g).IsNash s)
    (h : TenderHistory) (hh : ReachableHistory p h) (hopen : p.stop h = false)
    (i : Fin 2) (a : Bool) (x y : ℝ)
    (hbuyer : β (realQuotation h.state.quote) = .bargain i a x y)
    (hreject : ¬ AcceptsFollower P i (realQuotation h.state.quote) x y) :
    ((p.request h).includes i →
      ∃ d : TenderStrategy,
        (continuationGame P β p h).IsBestResponse (Function.update s i d) i ∧
        nextQuotation p (Function.update s i d) h i = h.state.quote i) ∧
    ((p.request h).includes (other i) →
      nextQuotation p s h (other i) < h.state.quote (other i)) := by sorry

end StrategicRFx.Benefit.Supplement
