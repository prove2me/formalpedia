-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_theorem_6
-- name    : StrategicRFx.Benefit.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:18:21.882499+00:00
-- url     : https://prove2.me/theorems/971880fe-5bdf-4346-ad80-fef14b9ab73a
-- title:
--   Theorem 6 — conditional unique outcome under any tendering and one-shot nonexistence
-- statement:
--   Let $\Pi$ be first-best chain profit, $\Pi^{-i}$ the exclusive profit without supplier $i$, and $\theta_i\in(0,1)$ the supplier bargaining powers, with the other source standing assumptions and technical buyer selector. Let $\pi^F$ be the most favorable bargaining outcome. Both conclusions are retained:
--
--   1. If a pure Nash equilibrium exists under one-shot simultaneous solicitation, then there is a nonnegative pair satisfying
--
--   $$\pi_i^F=\theta_i(\Pi-\pi_j^F-\Pi^{-i})^+\quad(\{i,j\}=\{1,2\}),$$
--
--   and this same pair is the unique pure equilibrium quotation outcome under every tendering procedure. The target includes existence under every procedure, as well as equality of every equilibrium outcome with that pair.
--
--   2. There is no one-shot simultaneous pure Nash equilibrium if both ordered-pair inequalities and the strict absolute-value inequality hold:
--
--   $$\Pi^{-i}<(1-\theta_j)\Pi+\theta_j\Pi^{-j}\quad(\{i,j\}=\{1,2\}),\qquad |\theta_1-\theta_2|>(1-\theta_1)(1-\theta_2).$$
--
--   The second conclusion is independent of the first sentence's existence premise. Deviations in the one-shot game range over every nonnegative real quote, and the source supplier tie preference includes the buyer’s acceptance hierarchy at equal profits. General procedures allow history-dependent revelation requests and stopping, retain constant-quote strategies, and are not restricted to one particular iterative schedule. A general procedure must stop once neither supplier changes his quote given the opponent's current quote, and must not deny a supplier responses forever along a continuing play.
--
--   Differences from the source:
--   - encoding: real nonnegative profit quotations and revealed requests → NNReal quotations, full public histories, arbitrary whole-strategy deviations, singleton or simultaneous requests; reason: retains the continuous quote domain and both request variants without a finite horizon
--   - reading: equilibrium and optimal responses considering future play → pure Nash optimality at the initial quotes and at every reachable public history; reason: p. 7 explicitly requires all potential outcomes, including off-path outcomes, to be subgame perfect; ec15–ec16 compare equilibrium future responses
--   - reading: procurement begins after tendering terminates; no transaction has zero profit → endless tendering has no final quote and all three no-transaction profits are explicitly zero; reason: extends p. 7 normalization to the operational boundary where negotiation never begins; the paper assigns no other outcome to a solicitation that never ends, and p. 7 normalizes every no-transaction profit to 0
--   - reading: any tendering procedure → public revelation and request rules admitting both initial quotes, constant-quote responses, upward or downward revisions in general procedures, fair continuing response opportunities and stopping once neither supplier changes his quote given the opponent's current quote; reason: includes one-shot, either alternating order, simultaneous requests and earlier stopping rules; the general class is no longer limited to monotone quotation revisions; the paper names no further property of a tendering procedure, and the ec23 proof uses only that a constant quote is always available
--   - encoding: an indifferent supplier quotes the price preferred by the buyer (p. 16) → primary-profit one-shot Nash plus the same buyer-profit/acceptance-priority tie preference used by the dynamic game; reason: retains accept-both and early acceptance at equal buyer profit, including zero supplier profit; does not add an epsilon or exclude real quotes
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Theorem 6, p. 20; proof pp. ec22–ec23

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Tendering

namespace StrategicRFx.Benefit.Supplement

/-- Theorem 6, p. 20; proof ec22–ec23. Both sentences are retained:
conditional existence and uniqueness at piF under every tendering procedure,
and the exact independent sufficient condition for one-shot nonexistence. -/
theorem theorem_6 (P : Params) (hP : Standing P) (β : BuyerSelector)
    (hβ : SourceBuyerSelector P β) :
    (((∃ x y : NNReal, IsOneShotEquilibrium P β x y) →
      ∃ qF : Quotation,
        (∀ i, (qF i : ℝ) = P.θ i * max (P.Pi - qF (other i) - P.PiEx i) 0) ∧
        (∀ p : TenderProcedure, ValidTenderProcedure p →
          ∃ s : TenderProfile, IsTenderEquilibrium P β p s ∧ finalQuotation p s = some qF) ∧
        (∀ p : TenderProcedure, ValidTenderProcedure p →
          ∀ s : TenderProfile, IsTenderEquilibrium P β p s → finalQuotation p s = some qF))) ∧
    (((∀ i : Fin 2, P.PiEx i < (1 - P.θ (other i)) * P.Pi +
          P.θ (other i) * P.PiEx (other i)) ∧
        |P.θ 0 - P.θ 1| > (1 - P.θ 0) * (1 - P.θ 1)) →
      ¬ ∃ x y : NNReal, IsOneShotEquilibrium P β x y) := by sorry

end StrategicRFx.Benefit.Supplement
