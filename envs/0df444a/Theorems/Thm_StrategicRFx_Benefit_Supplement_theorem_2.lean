-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_theorem_2
-- name    : StrategicRFx.Benefit.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:12:43.381199+00:00
-- url     : https://prove2.me/theorems/3e37138b-0da1-4cf7-812f-bfa9aac35fb6
-- title:
--   Theorem 2 — every sequential equilibrium coordinates, with or without RFx
-- statement:
--   Let revenue, production costs and bargaining powers satisfy the primitive source assumptions. Under sequential contract bargaining, either supplier may negotiate first. For every equilibrium without an RFx, and every negotiation-stage equilibrium after any nonnegative RFx quote pair, the actual quantity vector $\widehat q$ satisfies
--
--   $$\Pi(\widehat q)=\Pi(q^o),\qquad \widehat q=q^o.$$
--
--   Here $q^o$ is the unique interior maximizer of total supply-chain profit. Accepted RFx quotes remain binding fixed-quantity transactions if renegotiation fails; rejected quotes leave no deal. Both exclusive-sourcing cases, dual sourcing, and failure continuations are represented. The initial contract functions are unrestricted, and coordination is a conclusion rather than an equilibrium condition.
--
--   The quantity identity is equivalent to coordination under the source's uniqueness assumption. This theorem justifies reducing subsequent sequential bargaining analysis to profit allocations.
--
--   Differences from the source:
--   - encoding: suppliers 1 and 2 and nonnegative real quantities → Fin 2 suppliers; attained sourcing and exclusive-optimum relations; reason: preserves both suppliers and all quantities without default values for unattained maximizations
--   - reading: Assumption 2 says almost surely on a deterministic quantity domain → Lebesgue almost everywhere on the nonnegative quadrant; reason: the source supplies no random quantity law; no C² continuity is imposed
--   - encoding: accepted RFx quotation and subsequent renegotiation → a fixed-quantity, fixed-payment procurement right until replaced by a negotiated contingent contract; reason: retains the exact fallback obligations on pp. 15–18, including single sourcing and deal failure
--   - reading: multiple-valued follower contract in the sequential Nash programs → equilibria quantify over every consistent selection from the attained follower correspondence, with the same selection used for all comparisons; reason: retains arbitrary consistent follower choices from §2.3.2; selection is required only where an attained response exists, never a unique or universally attained optimum
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Theorem 2, p. 11; proof pp. ec2–ec4

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_RFContract

namespace StrategicRFx.Benefit.Supplement

/-- Theorem 2, p. 11; proof ec2–ec4. Every sequential equilibrium, for either
leader and with or without an RFx, has the unrestricted first-best quantity.
The RFx clause includes actual failed-renegotiation spot commitments. -/
theorem theorem_2 (M : Technology) (b : FirstBest) (hM : TechnologyAssumptions M b) :
    (∀ i x, IsSequentialWithoutRFx M i x →
      IsCoordinated M b x.order ∧ sourcingQuantity x.order = b.dual) ∧
    (∀ t i x, IsSequentialWithRFx M b t i x →
      IsCoordinated M b x.order ∧ sourcingQuantity x.order = b.dual) := by sorry

end StrategicRFx.Benefit.Supplement
