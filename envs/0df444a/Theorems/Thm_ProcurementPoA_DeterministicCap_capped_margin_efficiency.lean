-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_capped_margin_efficiency
-- name    : ProcurementPoA.DeterministicCap.capped_margin_efficiency
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-20T16:29:44.036685+00:00
-- url     : https://prove2.me/theorems/58135019-aa0e-4128-939a-1752b1bfefe7
-- title:
--   Proof of Lemma 5.2 — the capped auction is (1 − ε)-efficient on margins (Jin–Lu)
-- statement:
--   **Source.** Proof of Lemma 5.2 (Appendix A.1.1, p. 16): "Finally, we know that the value auction is $(1-\varepsilon)$-efficient [JL23a], so $\mathbb{E}[(T-c_{\mathrm{win}})\mathbf{1}_A] \ge (1-\varepsilon)\,\mathbb{E}[(T-C^\star)_+]$." Here $\varepsilon = 1/e^2$. The cited result is Jin and Lu, *First Price Auction is $1-1/e^2$ Efficient*, J. ACM 70(5), 2023 ([doi:10.1145/3617902](https://doi.org/10.1145/3617902)), Theorem 1. The paper applies it to the value auction with values $v_i = (T-c_i)_+$ and bids $(T-b_i)_+$.
--
--   **Statement.** There are $n+1$ suppliers. Their costs are independent with laws supported on measurable sets $\Theta_i \subseteq [1,R]$. The bids form a mixed profile $\sigma$, and $\tau$ is any measurable tie rule that selects a lowest bidder. Suppose $\sigma$ is a Bayes–Nash equilibrium of the first-price procurement auction with deterministic cap $T \ge 1$ (`ProcurementPoA.DeterministicCap.IsBNE`, the definition the mission's Lemma 5.2 uses):
--   - no supplier bids below cost;
--   - for every type, almost every bid used is a best response against every real deviation;
--   - a bid $a \le T$ earns $(a-c)$ times its interim winning probability, and a bid above $T$ earns $0$.
--
--   Then
--   $$(1-e^{-2})\,\mathbb{E}\big[(T-C^\star)_+\big] \;\le\; \mathbb{E}\Big[\mathbf 1\{\min_j b_j \le T\}\sum_i (T-c_i)_+\,\tau(b)(\{i\})\Big],$$
--   where $C^\star = \min_i c_i$, and the right side is the expectation under equilibrium play (costs, then bids, independent across suppliers). In words, the margin $T - c_{\mathrm{win}}$ of the accepted supplier is on average at least the fraction $1-e^{-2}$ of the best possible margin $(T - C^\star)_+$.
--
--   **Role.** This is the one step of the proof of Lemma 5.2 that the paper takes from Jin and Lu. Lemma 5.2 (`ProcurementPoA.DeterministicCap.lemma_5_2`) follows from it by the rest of the paper's argument: on the event $C^\star < T$ the lowest bid is accepted, and otherwise the social cost is at most $R$.
-- source:
--   S. Palazzotto and A. Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission 293, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, p. 16, proof of Lemma 5.2 (Appendix A.1.1), the step citing Jin and Lu [JL23a, Theorem 1]

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open MeasureTheory

namespace ProcurementPoA.DeterministicCap

theorem capped_margin_efficiency (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T)
    {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D 1 R) (heq : IsBNE D τ σ T) :
    ENNReal.ofReal (1 - epsilon) * ∫⁻ c, ENNReal.ofReal (T - lowest c) ∂(typeLaw D) ≤
      ∫⁻ x, (if lowest (fun i => (x i).2) ≤ T then
          ∑ i, ENNReal.ofReal (T - (x i).1) * τ.select (fun j => (x j).2) {i} else 0)
        ∂(playLaw D σ) := by sorry

end ProcurementPoA.DeterministicCap
