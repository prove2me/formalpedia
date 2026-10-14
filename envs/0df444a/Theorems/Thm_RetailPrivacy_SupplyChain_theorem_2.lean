-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_theorem_2
-- name    : RetailPrivacy.SupplyChain.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:45.453976+00:00
-- url     : https://prove2.me/theorems/de6deb9c-8d57-4729-a7c6-3e0967926d36
-- title:
--   Theorem 2, p. 23 — the GDPR's effect on consumers, retailer and supplier: triple win, triple lose and the mixed cases
-- statement:
--   Consider the online retail supply chain: the retailer decides whether to collect consumer data, the supplier sets a wholesale price, the retailer sets a retail price, and consumers with uniform inconvenience cost $\theta \in [0,1]$ buy and disclose or hide their data. Compare the ℝ mode (retailer-controlled data, before the GDPR) with the ℂ mode (consumer-controlled data, the GDPR). Let $c > 0$, $\delta \in (0,1)$, $v > 0$, and write
--   $$t_1 = \frac{4\sqrt{(1-\delta)\mathcal M}}{\mathcal Z},\quad t_2 = \frac{4\mathcal M\sqrt{1-\delta}}{\mathcal Z\sqrt{\mathcal F}},\quad t_3 = 4\sqrt{1-\delta},\quad t_4 = \frac{4\sqrt{\mathcal F}}{\mathcal Z},\quad t_5 = \frac{4\sqrt{\mathcal M}}{\mathcal Z}.$$
--   Subgame-perfect equilibria exist under both policies. Let $P_{\mathbb R}$ and $P_{\mathbb C}$ be any subgame-perfect equilibria under the ℝ and ℂ modes. Comparing the equilibrium consumer surplus, retailer profit and supplier profit of $P_{\mathbb C}$ with those of $P_{\mathbb R}$:
--
--   1. **Triple lose.** If $t_3 < v < t_4$, all three are strictly lower under the GDPR.
--   2. **Triple win.** If $v < t_1$, all three are strictly higher under the GDPR (a Pareto improvement).
--   3. **Other cases.**
--      - If $t_1 < v < t_2$, the GDPR strictly lowers the retailer's profit and strictly raises the consumer surplus and the supplier's profit.
--      - If $t_2 < v < t_3$, the GDPR strictly lowers the retailer's profit and the consumer surplus and strictly raises the supplier's profit.
--      - If $t_4 < v < t_5$, the GDPR strictly raises the consumer surplus and strictly lowers the retailer's and the supplier's profits.
--
--   The theorem shows that a privacy regulation that protects consumers in a single-firm market can, once an upstream supplier is present, hurt every party, including the consumers it is meant to protect.
--
--   **Formalization Note** The "hurts", "reduces" and "worse-off" of part (iii) are strict. The standing assumption $v > 0$ is added (at $v \le 0$ nothing is sold and all outcomes are zero). No tie-breaking rule is imposed: the open intervals avoid the points $t_3$ and $t_5$ where a retailer is indifferent about collecting. The existence conjuncts rule out a vacuous "every equilibrium".
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 23, Theorem 2; proof p. ec26

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem theorem_2 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .R v c δ P) ∧ (∃ P : Profile, IsSPE .C v c δ P) ∧
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (4 * Real.sqrt (1 - δ) < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PC < eqCS v δ PR ∧ eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqSupplier v δ PC < eqSupplier v δ PR) ∧
      (v < 4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PR < eqCS v δ PC ∧ eqRetailer v c δ PR < eqRetailer v c δ PC ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * Real.sqrt ((1 - δ) * RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) →
          eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqCS v δ PR < eqCS v δ PC ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * RetailPrivacy.SingleFirm.Mc c δ * Real.sqrt (1 - δ) / (RetailPrivacy.SingleFirm.Zc c δ * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ)) < v ∧ v < 4 * Real.sqrt (1 - δ) →
          eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqCS v δ PC < eqCS v δ PR ∧ eqSupplier v δ PR < eqSupplier v δ PC) ∧
      (4 * Real.sqrt (RetailPrivacy.SingleFirm.Fc c δ) / RetailPrivacy.SingleFirm.Zc c δ < v ∧ v < 4 * Real.sqrt (RetailPrivacy.SingleFirm.Mc c δ) / RetailPrivacy.SingleFirm.Zc c δ →
          eqCS v δ PR < eqCS v δ PC ∧ eqRetailer v c δ PC < eqRetailer v c δ PR ∧ eqSupplier v δ PC < eqSupplier v δ PR) := by sorry

end RetailPrivacy.SupplyChain
