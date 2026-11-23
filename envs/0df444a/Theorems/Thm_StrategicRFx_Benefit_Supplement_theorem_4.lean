-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_theorem_4
-- name    : StrategicRFx.Benefit.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:16:23.575468+00:00
-- url     : https://prove2.me/theorems/4805bcf1-a45d-487c-bf35-f5ca36117c83
-- title:
--   Theorem 4 — existence, unique outcome across iterative procedures and acceptance of both offers
-- statement:
--   Let the reduced bargaining parameters satisfy the source's standing assumptions. There exist a finite technical-selector construction, its supplier security response functions, and a nonnegative quote pair $q^*$, with at least one buyer selector satisfying the construction. For every such selector, the response functions secure each component of $q^*$ against every nonnegative opposing quote. For every iterative procedure, including either first mover, alternating requests and simultaneous requests,
--
--   $$\exists\sigma\in E,\ \operatorname{final}(\sigma)=q^*,\qquad
--   \forall\sigma\in E,\ \operatorname{final}(\sigma)=q^*,\qquad \text{the buyer accepts both quotes at }q^*.$$
--
--   Here $E$ is the set of sequentially rational pure-strategy equilibria of that procedure, computed from complete public histories and actual Nash-negotiation continuation payoffs. Thus equilibrium existence, finite stopping, uniqueness of the outcome and equality across procedures are conclusions. Strategies need not be unique. The finite cutoff construction and security responses are also conclusions, not assumptions hidden inside the game. Quotes above total first-best surplus use the source's high-quote extension.
--
--   Differences from the source:
--   - encoding: real nonnegative profit quotations and revealed requests → NNReal quotations, full public histories, arbitrary whole-strategy deviations, singleton or simultaneous requests; reason: retains the continuous quote domain and both request variants without a finite horizon
--   - reading: equilibrium and optimal responses considering future play → pure Nash optimality at the initial quotes and at every reachable public history; reason: p. 7 explicitly requires all potential outcomes, including off-path outcomes, to be subgame perfect; ec15–ec16 compare equilibrium future responses
--   - reading: procurement begins after tendering terminates; no transaction has zero profit → endless tendering has no final quote and all three no-transaction profits are explicitly zero; reason: extends p. 7 normalization to the operational boundary where negotiation never begins; the paper assigns no other outcome to a solicitation that never ends, and p. 7 normalizes every no-transaction profit to 0
--   - encoding: recursive response construction and any alternative iterative procedure → unbounded finite construction witnesses; existence of a valid selector and pointwise security responses; a common realized final quote for every fair iterative request rule; reason: retains all existence, uniqueness and invariance clauses without using the acceptance region as the definition of equilibrium
--   - reading: ec17 reverses the accept-both region inequalities and repeats index i in the second boundary term → use the two inequalities of Lemma 2 (p. 18), with the other supplier j in the second term of acceptanceBoundary; reason: solving the complete Lemma 2 system for quote i gives min(theta_i*(Pi-z-PiEx_i)^+, (Pi-PiEx_j-z/theta_j)^+); no source parameter or quotation is excluded
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Theorem 4, p. 19; proof pp. ec17–ec21

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Tendering

namespace StrategicRFx.Benefit.Supplement

/-- Theorem 4, p. 19; proof ec17–ec21. The finite selector construction,
consistent buyer selector and supplier security responses all exist. For
every iterative procedure a sequentially rational pure equilibrium exists,
all equilibria terminate at the same quotation, and both offers are accepted.
No finite horizon, security property or equilibrium existence is a premise. -/
theorem theorem_4 (P : Params) (hP : Standing P) :
    ∃ (c : SelectorConstruction) (ρ : Fin 2 → ℝ → ℝ) (q : Quotation),
      ValidSelectorConstruction P c ∧ SecurityResponse P c ρ ∧
      realQuotation q = c.quotes c.length ∧
      (∃ β : BuyerSelector, RespectsSelectorConstruction P c β) ∧
      ∀ β : BuyerSelector, RespectsSelectorConstruction P c β →
        (∀ i z, 0 ≤ z → 0 ≤ ρ i z ∧
          (q i : ℝ) ≤ ((β (quoteAt i (ρ i z) z)).payoff P (quoteAt i (ρ i z) z)).2 i) ∧
        (∀ p : TenderProcedure, IterativeTenderProcedure p →
          ∃ s : TenderProfile, IsTenderEquilibrium P β p s ∧ finalQuotation p s = some q) ∧
        (∀ p : TenderProcedure, IterativeTenderProcedure p →
          ∀ s : TenderProfile, IsTenderEquilibrium P β p s → finalQuotation p s = some q) ∧
        β (realQuotation q) = .both ∧ AcceptsBoth P (realQuotation q) := by sorry

end StrategicRFx.Benefit.Supplement
