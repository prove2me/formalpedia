-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_Supplement_theorem_3
-- name    : StrategicRFx.Benefit.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:13:49.916301+00:00
-- url     : https://prove2.me/theorems/a8a1613d-9959-46d9-98b2-251245d2b79b
-- title:
--   Theorem 3 — exact cost-plus replacement in all bargaining settings
-- statement:
--   Let the primitive source assumptions hold, and let $(\widehat C_1,\widehat C_2)$ be any coordinated equilibrium, either simultaneous or sequential with or without an RFx, in either negotiation order. Write $\widehat\pi_0,\widehat\pi_1,\widehat\pi_2$ for its three normal payoffs and $\widehat\pi_0^{-j}$ for the original exclusive buyer payoff with supplier $i$, where $\{i,j\}=\{1,2\}$. Replace all four transfers by
--
--   $$\check T_i(q)=C_i(q)+\widehat\pi_i,\qquad
--   \check T_i^{-j}(q)=C_i(q)+\Pi^{-j}-\widehat\pi_0^{-j}\quad (i=1,2).$$
--
--   These exact replacement contracts are an equilibrium in the same bargaining setting. They preserve every normal player payoff and the buyer's two exclusive payoffs:
--
--   $$\check\pi_k=\widehat\pi_k\quad(k=0,1,2),\qquad
--   \check\pi_0^{-j}=\widehat\pi_0^{-j}\quad(j=1,2).$$
--
--   The constructor uses the source first-best normal and exclusive procurement quantities as maximizing witnesses. This implements the full coordinated equilibrium payoff with cost-plus contracts; it does not restrict the original equilibrium to that contract class.
--
--   Differences from the source:
--   - encoding: suppliers 1 and 2 and nonnegative real quantities → Fin 2 suppliers; attained sourcing and exclusive-optimum relations; reason: preserves both suppliers and all quantities without default values for unattained maximizations
--   - reading: Assumption 2 says almost surely on a deterministic quantity domain → Lebesgue almost everywhere on the nonnegative quadrant; reason: the source supplies no random quantity law; no C² continuity is imposed
--   - encoding: the displayed replacement contract is also an equilibrium with the same profit → the computed four transfers, first-best order witnesses, equality of all three normal payoffs and both exclusive buyer payoffs; reason: the displayed formulas and the first paragraph of the ec4 proof specify these exact transfers and exclusive payoff identities
--   - reading: multiple-valued follower contract in the sequential Nash programs → equilibria quantify over every consistent selection from the attained follower correspondence, with the same selection used for all comparisons; reason: retains arbitrary consistent follower choices from §2.3.2; selection is required only where an attained response exists, never a unique or universally attained optimum
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Theorem 3, p. 11; proof pp. ec4–ec5

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Supplement_RFContract

namespace StrategicRFx.Benefit.Supplement

/-- Theorem 3, p. 11; proof ec4–ec5. The replacement is computed, including
both exclusive markups, and works in every source bargaining setting. -/
theorem theorem_3 (M : Technology) (b : FirstBest) (hM : TechnologyAssumptions M b)
    (setting : ContractSetting) (x : ContractOutcome)
    (hx : IsContractEquilibrium M b setting x) (hc : IsCoordinated M b x.order) :
    IsContractEquilibrium M b setting (costPlusOutcome M b x) ∧
    (costPlusOutcome M b x).payoff M = x.payoff M ∧
    (∀ i, (exclusivePayoff M ((costPlusOutcome M b x).contracts i) i
        ((costPlusOutcome M b x).exclusiveOrder i)).buyer =
      (exclusivePayoff M (x.contracts i) i (x.exclusiveOrder i)).buyer) ∧
    (∀ i, IsCostPlus M i ((costPlusOutcome M b x).contracts i)) := by sorry

end StrategicRFx.Benefit.Supplement
