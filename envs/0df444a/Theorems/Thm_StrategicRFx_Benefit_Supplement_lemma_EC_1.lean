-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_lemma_EC_1
-- name    : StrategicRFx.Benefit.Supplement.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:11:28.919377+00:00
-- url     : https://prove2.me/theorems/58b7ea65-4da6-44ae-a2e2-27c722516a1f
-- title:
--   Lemma EC.1 — strict dual-sourcing improvement and weak coordinated cost-plus improvement
-- statement:
--   Let the primitive revenue, costs and bargaining powers satisfy the standing source assumptions. Consider all simultaneous equilibria over the unrestricted quantity-dependent contract class. Then:
--
--   1. Every single-sourcing equilibrium has a dual-sourcing equilibrium with all three payoffs weakly larger and at least one strictly larger.
--   2. Every dual-sourcing equilibrium has a coordinated equilibrium implemented by cost-plus contracts with all three payoffs weakly larger.
--
--   Writing $v$ for the original three-player payoff vector and $w$ for the improved vector, the improvement requirements are
--
--   $$w\ge v,\quad w\ne v\quad\text{in (1)},\qquad w\ge v\quad\text{in (2)}.$$
--
--   The second equilibrium has total chain profit equal to the unrestricted first best. This is the source support for coordination in Pareto equilibrium. Neither coordination nor cost-plus implementation is built into the initial equilibrium predicate.
--
--   Differences from the source:
--   - encoding: suppliers 1 and 2 and nonnegative real quantities → Fin 2 suppliers; attained sourcing and exclusive-optimum relations; reason: preserves both suppliers and all quantities without default values for unattained maximizations
--   - reading: Assumption 2 says almost surely on a deterministic quantity domain → Lebesgue almost everywhere on the nonnegative quadrant; reason: the source supplies no random quantity law; no C² continuity is imposed
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Lemma EC.1, p. ec1

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Simultaneous

namespace StrategicRFx.Benefit.Supplement

theorem lemma_EC_1 (M : Technology) (b : FirstBest) (h : TechnologyAssumptions M b) :
    (∀ x, IsSimultaneous M x → (∃ i q, x.order = .single i q) →
      ∃ y, IsSimultaneous M y ∧ (∃ q, y.order = .dual q) ∧
        StrictlyImproves (y.payoff M) (x.payoff M)) ∧
    (∀ x, IsSimultaneous M x → (∃ q, x.order = .dual q) →
      ∃ y, IsSimultaneous M y ∧ IsCoordinated M b y.order ∧
        (∀ i, IsCostPlus M i (y.contracts i)) ∧ WeaklyImproves (y.payoff M) (x.payoff M)) := by sorry

end StrategicRFx.Benefit.Supplement
