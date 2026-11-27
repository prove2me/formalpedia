-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_theorem_1
-- name    : StrategicRFx.Benefit.Supplement.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:12:08.908793+00:00
-- url     : https://prove2.me/theorems/26eafe01-abbd-4da1-98c4-77b86b57bb72
-- title:
--   Theorem 1 — Every Pareto equilibrium of simultaneous contract bargaining coordinates the chain.
-- statement:
--   Let revenue, costs and bargaining powers satisfy the primitive source assumptions, and let the buyer and two suppliers be in a Pareto-undominated simultaneous contract-bargaining equilibrium. If $\widehat q$ is its actual procurement quantity vector and $q^o$ is the unique interior first best, then
--
--   $$\Pi(\widehat q)=\Pi(q^o).$$
--
--   Thus the supply chain is coordinated. Pareto comparison ranges over equilibria of the same unrestricted contract model, not over arbitrary payoff vectors. The equilibrium predicate does not assume coordination.
--
--   Differences from the source:
--   - encoding: suppliers 1 and 2 and nonnegative real quantities → Fin 2 suppliers; attained sourcing and exclusive-optimum relations; reason: preserves both suppliers and all quantities without default values for unattained maximizations
--   - reading: Assumption 2 says almost surely on a deterministic quantity domain → Lebesgue almost everywhere on the nonnegative quadrant; reason: the source supplies no random quantity law; no C² continuity is imposed
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Theorem 1, p. 11

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_Simultaneous

namespace StrategicRFx.Benefit.Supplement

theorem theorem_1 (M : Technology) (b : FirstBest) (h : TechnologyAssumptions M b)
    (x : ContractOutcome) (hx : IsParetoSimultaneous M x) :
    IsCoordinated M b x.order := by sorry

end StrategicRFx.Benefit.Supplement
